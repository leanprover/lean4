// Lean compiler output
// Module: Lean.Elab.Inductive
// Imports: Init Lean.Util.ReplaceLevel Lean.Util.ReplaceExpr Lean.Util.CollectLevelParams Lean.Util.Constructions Lean.Elab.Command Lean.Elab.CollectFVars Lean.Elab.DefView Lean.Elab.DeclUtil
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
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2;
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType___at_Lean_Elab_Term_ensureType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__6;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__4;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_27__withUsed(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___closed__1;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_InductiveView_inhabited;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Attribute_inhabited;
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_28__updateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_27__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__10;
lean_object* l_Std_HashMapImp_insert___at___private_Lean_MetavarContext_2__visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1;
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Inductive_26__removeUnused___closed__1;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_ElabHeaderResult_inhabited;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__9;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__8;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_ibelow(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CtorView_inhabited;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__7;
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1;
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_FS_Handle_putStrLn___rarg___closed__1;
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6;
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_below(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___main(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(lean_object*, size_t, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux(lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__2;
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_5__mkTypeFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__2;
extern lean_object* l_Lean_MonadCacheT_MonadLift___closed__1;
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_26__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributes___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__1;
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_30__mkIndFVar2Const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__11;
lean_object* lean_mk_brec_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_MonadError___closed__3;
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_32__mkCtor2InferMod___boxed(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1;
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributes___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_27__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1;
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__6;
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___main___rarg___closed__18;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__5;
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_Inductive_28__updateParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1(lean_object*);
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_30__mkIndFVar2Const___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_prodToExpr___rarg___lambda__1___closed__2;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_binduction_on(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2;
lean_object* l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Inductive_32__mkCtor2InferMod(lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1;
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ReaderT_MonadLift___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_MetavarContext_2__visit___spec__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
lean_object* l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1;
extern uint8_t l_Bool_Inhabited;
lean_object* l___private_Lean_Elab_Inductive_25__collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1;
lean_object* lean_get_stdout(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
extern lean_object* l_Std_HashMap_find_x21___rarg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__8;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__7;
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_12__elabHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__9;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1;
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
lean_object* l___private_Lean_Elab_Inductive_33__applyInferMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__4;
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_replace___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_25__collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__5;
lean_object* l___private_Lean_Elab_Inductive_33__applyInferMod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit___main(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_26__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8;
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam;
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__12;
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_35 == 0)
{
x_5 = x_4;
goto block_33;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__6;
x_37 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_36, x_2, x_3, x_4);
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
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__9;
x_43 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_42, x_2, x_3, x_4);
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
block_33:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_12, x_2, x_3, x_5);
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_Elab_Attribute_inhabited;
x_19 = lean_array_get(x_18, x_6, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_registerClassAttr___closed__2;
x_22 = lean_name_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
x_24 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_23, x_2, x_3, x_5);
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
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_27 == 0)
{
x_5 = x_4;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Elab_Command_checkValidCtorModifier___closed__9;
x_29 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_28, x_2, x_3, x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Elab_Command_checkValidCtorModifier___closed__12;
x_35 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_34, x_2, x_3, x_4);
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
block_25:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
x_12 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_11, x_2, x_3, x_5);
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Elab_Command_checkValidCtorModifier___closed__6;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_19, x_2, x_3, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_4 = 0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CtorView_inhabited___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_InductiveView_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_3);
lean_ctor_set(x_7, 6, x_1);
lean_ctor_set(x_7, 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_InductiveView_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Expr_Inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_1, x_4, x_5, x_6, x_7, x_20);
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
x_42 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_1, x_4, x_5, x_6, x_7, x_41);
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
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, resultant type is not a sort");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_6);
x_14 = l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_1, 6);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_6);
x_18 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkLevelSucc(x_19);
x_22 = l_Lean_mkSort(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_16);
lean_ctor_set(x_25, 3, x_5);
lean_ctor_set(x_25, 4, x_22);
x_26 = lean_array_push(x_3, x_25);
x_27 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_4, x_24, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_33 = l_Lean_Elab_Term_elabTerm(x_30, x_31, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_34);
x_36 = l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1(x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3;
x_41 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_30, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_30);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_30);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_2, x_47);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_13);
lean_ctor_set(x_49, 2, x_28);
lean_ctor_set(x_49, 3, x_5);
lean_ctor_set(x_49, 4, x_34);
x_50 = lean_array_push(x_3, x_49);
x_51 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_4, x_48, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_28);
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
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
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
lean_dec(x_30);
lean_dec(x_28);
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
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
return x_33;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed), 12, 4);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_1);
x_18 = l_Lean_Elab_Term_elabBinders___rarg(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
return x_18;
}
}
}
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_1__elabHeaderAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, number of parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3;
x_22 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_3 = x_28;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(x_13, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
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
else
{
uint8_t x_19; 
lean_dec(x_13);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2 + 3);
lean_dec(x_17);
if (x_18 == 0)
{
if (x_1 == 0)
{
uint8_t x_31; 
x_31 = 1;
x_19 = x_31;
goto block_30;
}
else
{
uint8_t x_32; 
x_32 = 0;
x_19 = x_32;
goto block_30;
}
}
else
{
if (x_1 == 0)
{
uint8_t x_33; 
x_33 = 0;
x_19 = x_33;
goto block_30;
}
else
{
uint8_t x_34; 
x_34 = 1;
x_19 = x_34;
goto block_30;
}
}
block_30:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3;
x_22 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_3 = x_28;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2 + 3);
lean_dec(x_13);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(x_14, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, universe parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3;
x_20 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_3, x_25);
lean_dec(x_3);
x_3 = x_26;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_lt(x_10, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Elab_Command_InductiveView_inhabited;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(x_17, x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_17);
return x_18;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_4__checkLevelNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_5__mkTypeFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(x_9, x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_7__getResultingType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Inductive_7__getResultingType___closed__1;
x_10 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_7__getResultingType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isDefEqNoConstantApprox___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resulting universe mismatch, given ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_11 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_indentExpr(x_1);
x_16 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_MessageData_ofList___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_forallTelescopeCompatibleAux___main___rarg___closed__18;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_3);
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2___boxed), 10, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_4, x_11, x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3___boxed), 10, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l_Array_empty___closed__1;
x_13 = l_Lean_Meta_forallTelescopeCompatibleAux___main___rarg(x_11, x_3, x_1, x_2, x_12, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_18, 1, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_33 = x_18;
} else {
 lean_dec_ref(x_18);
 x_33 = lean_box(0);
}
x_34 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_13, 0);
lean_dec(x_39);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Inductive_5__mkTypeFor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_8, 3);
x_23 = l_Lean_replaceRef(x_20, x_22);
lean_dec(x_20);
x_24 = l_Lean_replaceRef(x_23, x_22);
lean_dec(x_23);
x_25 = l_Lean_replaceRef(x_24, x_22);
lean_dec(x_22);
lean_dec(x_24);
lean_ctor_set(x_8, 3, x_25);
lean_inc(x_18);
x_26 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_18);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_18);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
x_37 = lean_ctor_get(x_8, 2);
x_38 = lean_ctor_get(x_8, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_39 = l_Lean_replaceRef(x_20, x_38);
lean_dec(x_20);
x_40 = l_Lean_replaceRef(x_39, x_38);
lean_dec(x_39);
x_41 = l_Lean_replaceRef(x_40, x_38);
lean_dec(x_38);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_41);
lean_inc(x_18);
x_43 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_42, x_9, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_18);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
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
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_10__checkHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_17 = lean_array_get(x_16, x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Elab_Inductive_10__checkHeader(x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_11__checkHeaders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_12__elabHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_lt(x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_18; 
lean_free_object(x_11);
lean_inc(x_2);
x_18 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_13, x_21, x_9, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_13);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
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
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_2);
x_47 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_41, x_50, x_9, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_63 = x_49;
} else {
 lean_dec_ref(x_49);
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
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_47, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_67 = x_47;
} else {
 lean_dec_ref(x_47);
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
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_6);
x_17 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_3, x_4, x_5, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_apply_9(x_3, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_1, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed), 13, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_5);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(x_17, x_20, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg), 12, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_Inductive_5__mkTypeFor(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = x_23;
x_27 = lean_array_fset(x_16, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_replaceRef(x_1, x_6);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 3);
x_17 = l_Lean_replaceRef(x_14, x_16);
lean_dec(x_14);
x_18 = l_Lean_replaceRef(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
lean_ctor_set(x_11, 3, x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_2, x_3, x_4, x_19, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 2);
x_24 = lean_ctor_get(x_11, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_25 = l_Lean_replaceRef(x_14, x_24);
lean_dec(x_14);
x_26 = l_Lean_replaceRef(x_25, x_24);
lean_dec(x_24);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_2, x_3, x_4, x_28, x_5, x_7, x_8, x_9, x_10, x_27, x_12, x_13);
return x_29;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_10 = x_1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = x_12;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_7(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_18 = lean_array_get(x_17, x_1, x_11);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_empty___closed__1;
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1___boxed), 13, 5);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_19);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_24);
x_26 = l_Lean_Elab_Term_MonadError___closed__3;
x_27 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(x_20, x_21, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1___boxed), 10, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_15__isInductiveFamily___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor resulting type must be specified in inductive family declaration");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type, type expected");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 3);
x_17 = l_Lean_replaceRef(x_13, x_16);
lean_dec(x_13);
x_18 = l_Lean_replaceRef(x_17, x_16);
lean_dec(x_17);
x_19 = l_Lean_replaceRef(x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
lean_ctor_set(x_10, 3, x_19);
if (lean_obj_tag(x_14) == 0)
{
if (x_3 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_44, x_4);
x_20 = x_45;
x_21 = x_12;
goto block_43;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3;
x_47 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
lean_dec(x_14);
x_53 = lean_box(0);
x_54 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Elab_Term_elabTerm(x_52, x_53, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l___private_Lean_Elab_Inductive_7__getResultingType___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
x_59 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_56, x_58, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_getAppFn___main(x_60);
x_63 = lean_expr_eqv(x_62, x_4);
lean_dec(x_4);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = l_Lean_indentExpr(x_60);
x_65 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_60);
x_72 = l_Lean_Meta_isType___at_Lean_Elab_Term_ensureType___spec__1(x_60, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = l_Lean_indentExpr(x_60);
x_77 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_78, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_60);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_dec(x_72);
x_20 = x_56;
x_21 = x_84;
goto block_43;
}
}
else
{
uint8_t x_85; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
return x_72;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_72, 0);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_72);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_59);
if (x_89 == 0)
{
return x_59;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_59, 0);
x_91 = lean_ctor_get(x_59, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_59);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_55);
if (x_93 == 0)
{
return x_55;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_55, 0);
x_95 = lean_ctor_get(x_55, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_55);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
block_43:
{
lean_object* x_22; 
lean_inc(x_8);
lean_inc(x_6);
x_22 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_5, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_10, 0);
x_98 = lean_ctor_get(x_10, 1);
x_99 = lean_ctor_get(x_10, 2);
x_100 = lean_ctor_get(x_10, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_10);
x_101 = l_Lean_replaceRef(x_13, x_100);
lean_dec(x_13);
x_102 = l_Lean_replaceRef(x_101, x_100);
lean_dec(x_101);
x_103 = l_Lean_replaceRef(x_102, x_100);
lean_dec(x_100);
lean_dec(x_102);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_103);
if (lean_obj_tag(x_14) == 0)
{
if (x_3 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_126, x_4);
x_105 = x_127;
x_106 = x_12;
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3;
x_129 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_128, x_6, x_7, x_8, x_9, x_104, x_11, x_12);
lean_dec(x_11);
lean_dec(x_104);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_14, 0);
lean_inc(x_134);
lean_dec(x_14);
x_135 = lean_box(0);
x_136 = 1;
lean_inc(x_11);
lean_inc(x_104);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_137 = l_Lean_Elab_Term_elabTerm(x_134, x_135, x_136, x_6, x_7, x_8, x_9, x_104, x_11, x_12);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l___private_Lean_Elab_Inductive_7__getResultingType___closed__1;
lean_inc(x_11);
lean_inc(x_104);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_138);
x_141 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_138, x_140, x_6, x_7, x_8, x_9, x_104, x_11, x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Expr_getAppFn___main(x_142);
x_145 = lean_expr_eqv(x_144, x_4);
lean_dec(x_4);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_138);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_146 = l_Lean_indentExpr(x_142);
x_147 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6;
x_148 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_148, x_6, x_7, x_8, x_9, x_104, x_11, x_143);
lean_dec(x_11);
lean_dec(x_104);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
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
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; 
lean_inc(x_11);
lean_inc(x_104);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_142);
x_154 = l_Lean_Meta_isType___at_Lean_Elab_Term_ensureType___spec__1(x_142, x_6, x_7, x_8, x_9, x_104, x_11, x_143);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_138);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = l_Lean_indentExpr(x_142);
x_159 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9;
x_160 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_160, x_6, x_7, x_8, x_9, x_104, x_11, x_157);
lean_dec(x_11);
lean_dec(x_104);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_142);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
lean_dec(x_154);
x_105 = x_138;
x_106 = x_166;
goto block_125;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec(x_104);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_154, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_169 = x_154;
} else {
 lean_dec_ref(x_154);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_138);
lean_dec(x_104);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_141, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_141, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_173 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_104);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_ctor_get(x_137, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_137, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_177 = x_137;
} else {
 lean_dec_ref(x_137);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
block_125:
{
lean_object* x_107; 
lean_inc(x_8);
lean_inc(x_6);
x_107 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_5, x_105, x_6, x_7, x_8, x_9, x_104, x_11, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_108, x_6, x_7, x_8, x_9, x_104, x_11, x_109);
lean_dec(x_11);
lean_dec(x_104);
lean_dec(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
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
x_114 = lean_ctor_get(x_1, 2);
lean_inc(x_114);
lean_dec(x_1);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_112);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_1);
x_117 = lean_ctor_get(x_110, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
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
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_107, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_123 = x_107;
} else {
 lean_dec_ref(x_107);
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed), 12, 4);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_elabBinders___rarg(x_18, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_22);
lean_free_object(x_4);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
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
lean_free_object(x_4);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_ctor_get(x_38, 3);
lean_inc(x_40);
x_41 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
x_42 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_43 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed), 12, 4);
lean_closure_set(x_43, 0, x_38);
lean_closure_set(x_43, 1, x_2);
lean_closure_set(x_43, 2, x_42);
lean_closure_set(x_43, 3, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Elab_Term_elabBinders___rarg(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
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
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_array_get_size(x_2);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_12, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_Inductive_15__isInductiveFamily(x_13, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_11, 7);
x_23 = l_Array_toList___rarg(x_22);
x_24 = lean_unbox(x_20);
lean_dec(x_20);
x_25 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_24, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
x_32 = lean_ctor_get(x_8, 2);
x_33 = lean_ctor_get(x_8, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_34 = l_Lean_replaceRef(x_12, x_33);
x_35 = l_Lean_replaceRef(x_34, x_33);
lean_dec(x_34);
x_36 = l_Lean_replaceRef(x_35, x_33);
lean_dec(x_33);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_36);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l___private_Lean_Elab_Inductive_15__isInductiveFamily(x_13, x_1, x_4, x_5, x_6, x_7, x_37, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_11, 7);
x_42 = l_Array_toList___rarg(x_41);
x_43 = lean_unbox(x_39);
lean_dec(x_39);
x_44 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_43, x_42, x_4, x_5, x_6, x_7, x_37, x_9, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_16__elabCtors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_13, 1, x_18);
x_20 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_levelMVarToParam_x27(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_32);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
lean_inc(x_3);
x_43 = l_Lean_Elab_Term_levelMVarToParam_x27(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
x_21 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_13, 2, x_22);
lean_ctor_set(x_13, 1, x_19);
x_24 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_inc(x_3);
x_34 = l_Lean_Elab_Term_levelMVarToParam_x27(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_3);
x_37 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_40);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
lean_inc(x_3);
x_52 = l_Lean_Elab_Term_levelMVarToParam_x27(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_3);
x_55 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 3, 0);
} else {
 x_58 = x_51;
}
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_56);
x_59 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_18__levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected empty inductive declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive type resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Inductive_7__getResultingType___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 3)
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6;
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
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
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tmp_ind_univ_param");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_tmpIndParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__2;
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__3;
return x_1;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_7, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_27, x_4, x_5, x_6, x_7, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = l_Lean_TraceState_Inhabited___closed__1;
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_st_ref_set(x_7, x_38, x_15);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_get(x_5, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_47, x_4, x_5, x_6, x_7, x_43);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot infer resulting universe level of inductive datatype, given level contains metavariables ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", provide universe explicitly");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Level_hasMVar(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_2);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; 
lean_free_object(x_9);
x_16 = l_Lean_Level_getLevelOffset___main(x_11);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_tmpIndParam;
x_19 = l_Lean_Elab_Term_assignLevelMVar(x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_28 = l_Lean_mkSort(x_11);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l_Lean_Level_hasMVar(x_35);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_2);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Level_getLevelOffset___main(x_35);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Command_tmpIndParam;
x_44 = l_Lean_Elab_Term_assignLevelMVar(x_42, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = 1;
x_48 = lean_box(x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
x_50 = l_Lean_mkSort(x_35);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_shouldInferResultUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = lean_level_eq(x_2, x_8);
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
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of inductive datatype, provide universe explicitly");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_1 = x_6;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_level_eq(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_4, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_3);
x_22 = l_Lean_Elab_Command_accLevelAtCtor___main(x_20, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_21);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_1 = x_21;
x_4 = x_26;
goto _start;
}
}
default: 
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_3, x_28);
lean_dec(x_3);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_array_push(x_4, x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_4);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_1);
x_35 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_level_eq(x_1, x_2);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_push(x_4, x_1);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_4);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_4);
lean_dec(x_1);
x_42 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
return x_43;
}
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_expr_instantiate1(x_1, x_6);
x_15 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_2, x_3, x_4, x_14, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_expr_instantiate1(x_1, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_2, x_3, x_14, x_13, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
x_21 = (uint8_t)((x_18 << 24) >> 61);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed), 13, 5);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_20);
lean_closure_set(x_22, 4, x_5);
x_23 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(x_15, x_21, x_16, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_26);
x_29 = l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_6);
x_32 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_2);
x_35 = l_Lean_Elab_Command_accLevelAtCtor___main(x_33, x_1, x_2, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = (uint8_t)((x_28 << 24) >> 61);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed), 12, 4);
lean_closure_set(x_42, 0, x_27);
lean_closure_set(x_42, 1, x_1);
lean_closure_set(x_42, 2, x_2);
lean_closure_set(x_42, 3, x_40);
x_43 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_20__elabImplicitLambda___main___spec__1___rarg(x_25, x_41, x_26, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_12);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_16, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_18;
x_5 = x_15;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_18;
x_5 = x_15;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Array_empty___closed__1;
x_13 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(x_1, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_22__collectUniverses(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_tmpIndParam;
x_4 = lean_level_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Level_replace___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Level_replace___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ptr_addr(x_3);
x_7 = x_2 == 0 ? 0 : x_6 % x_2;
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_uget(x_8, x_7);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = x_10 == x_6;
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace___main(x_5, x_12);
lean_inc(x_3);
x_14 = lean_expr_update_sort(x_3, x_13);
x_15 = lean_array_uset(x_8, x_7, x_3);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_14);
x_17 = lean_array_uset(x_16, x_7, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_20);
lean_inc(x_3);
x_22 = lean_expr_update_const(x_3, x_21);
x_23 = lean_array_uset(x_8, x_7, x_3);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_22);
x_25 = lean_array_uset(x_24, x_7, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_5);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_29, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_3);
x_38 = lean_array_uset(x_37, x_7, x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_expr_update_app(x_3, x_31, x_35);
lean_inc(x_40);
x_41 = lean_array_uset(x_39, x_7, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_array_uset(x_45, x_7, x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_update_app(x_3, x_31, x_43);
lean_inc(x_48);
x_49 = lean_array_uset(x_47, x_7, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_5);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_52, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_3);
x_63 = lean_array_uset(x_62, x_7, x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = (uint8_t)((x_54 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_56, x_60);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_7, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = lean_array_uset(x_71, x_7, x_3);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_54 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_3, x_74, x_56, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_7, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_5);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_79, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_inc(x_3);
x_90 = lean_array_uset(x_89, x_7, x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = (uint8_t)((x_81 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_83, x_87);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_7, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_85, 1, x_95);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_7, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = (uint8_t)((x_81 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_83, x_96);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_7, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
case 8:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_5);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 3);
lean_inc(x_108);
lean_inc(x_1);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_106, x_4);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_107, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_108, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_7, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_let(x_3, x_110, x_113, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_7, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_7, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_let(x_3, x_110, x_113, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_7, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_5);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_7, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_mdata(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_7, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_7, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_mdata(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_7, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_5);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_154, x_4);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_inc(x_3);
x_160 = lean_array_uset(x_159, x_7, x_3);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_expr_update_proj(x_3, x_157);
lean_inc(x_162);
x_163 = lean_array_uset(x_161, x_7, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_155, 1, x_164);
lean_ctor_set(x_155, 0, x_162);
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_155, 0);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_3);
x_168 = lean_array_uset(x_167, x_7, x_3);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_expr_update_proj(x_3, x_165);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_7, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 12:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_174 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__4;
x_175 = l_unreachable_x21___rarg(x_174);
x_176 = lean_apply_1(x_175, x_4);
return x_176;
}
default: 
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_7);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Level_replace___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Level_replace___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ptr_addr(x_3);
x_7 = x_2 == 0 ? 0 : x_6 % x_2;
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_uget(x_8, x_7);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = x_10 == x_6;
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace___main(x_5, x_12);
lean_inc(x_3);
x_14 = lean_expr_update_sort(x_3, x_13);
x_15 = lean_array_uset(x_8, x_7, x_3);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_14);
x_17 = lean_array_uset(x_16, x_7, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_20);
lean_inc(x_3);
x_22 = lean_expr_update_const(x_3, x_21);
x_23 = lean_array_uset(x_8, x_7, x_3);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_22);
x_25 = lean_array_uset(x_24, x_7, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_5);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_29, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_3);
x_38 = lean_array_uset(x_37, x_7, x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_expr_update_app(x_3, x_31, x_35);
lean_inc(x_40);
x_41 = lean_array_uset(x_39, x_7, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_array_uset(x_45, x_7, x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_update_app(x_3, x_31, x_43);
lean_inc(x_48);
x_49 = lean_array_uset(x_47, x_7, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_5);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_52, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_3);
x_63 = lean_array_uset(x_62, x_7, x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = (uint8_t)((x_54 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_56, x_60);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_7, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = lean_array_uset(x_71, x_7, x_3);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_54 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_3, x_74, x_56, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_7, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_5);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_79, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_inc(x_3);
x_90 = lean_array_uset(x_89, x_7, x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = (uint8_t)((x_81 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_83, x_87);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_7, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_85, 1, x_95);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_7, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = (uint8_t)((x_81 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_83, x_96);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_7, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
case 8:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_5);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 3);
lean_inc(x_108);
lean_inc(x_1);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_106, x_4);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_107, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_108, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_7, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_let(x_3, x_110, x_113, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_7, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_7, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_let(x_3, x_110, x_113, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_7, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_5);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_7, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_mdata(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_7, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_7, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_mdata(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_7, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_5);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_154, x_4);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_inc(x_3);
x_160 = lean_array_uset(x_159, x_7, x_3);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_expr_update_proj(x_3, x_157);
lean_inc(x_162);
x_163 = lean_array_uset(x_161, x_7, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_155, 1, x_164);
lean_ctor_set(x_155, 0, x_162);
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_155, 0);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_3);
x_168 = lean_array_uset(x_167, x_7, x_3);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_expr_update_proj(x_3, x_165);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_7, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 12:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_174 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__4;
x_175 = l_unreachable_x21___rarg(x_174);
x_176 = lean_apply_1(x_175, x_4);
return x_176;
}
default: 
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_7);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_11 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_6, 1, x_12);
x_13 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_18 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_2, x_14);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_28 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_2, x_25, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_2, x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 2);
x_10 = 8192;
x_11 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_12 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_10, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_10, x_9);
lean_ctor_set(x_5, 2, x_14);
lean_ctor_set(x_5, 1, x_13);
x_15 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_7);
lean_ctor_set(x_2, 1, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_20 = 8192;
x_21 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_22 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_20, x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_1);
x_24 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_20, x_19);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_16);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_32 = x_27;
} else {
 lean_dec_ref(x_27);
 x_32 = lean_box(0);
}
x_33 = 8192;
x_34 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_35 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_33, x_30, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_1);
x_37 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_33, x_31);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 3, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_Inductive_19__getResultingUniverse(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_34; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux___main(x_11, x_13);
x_15 = l_Lean_Level_getLevelOffset___main(x_11);
lean_dec(x_11);
x_34 = l_Lean_Level_isParam(x_15);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_35 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
x_16 = x_12;
goto block_33;
}
block_33:
{
lean_object* x_17; 
lean_inc(x_2);
x_17 = l___private_Lean_Elab_Inductive_22__collectUniverses(x_15, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Array_toList___rarg(x_19);
lean_dec(x_19);
x_21 = l_Lean_Level_mkNaryMax___main(x_20);
x_22 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_21, x_2);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = l_Array_toList___rarg(x_23);
lean_dec(x_23);
x_26 = l_Lean_Level_mkNaryMax___main(x_25);
x_27 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_26, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_get_stdout(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg(x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_apply_2(x_12, x_1, x_11);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_io_error_to_string(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_io_error_to_string(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_IO_FS_Handle_putStrLn___rarg___closed__1;
x_12 = l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_12;
}
else
{
uint8_t x_13; 
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
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  >> ");
return x_1;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_expr_dbg_to_string(x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_1 = x_12;
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_1 = x_12;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_getStdout___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_print___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_println___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_24__traceIndTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_13;
x_9 = x_16;
goto _start;
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_3);
x_18 = l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_1 = x_13;
x_9 = x_19;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_25__collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_25__collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_25__collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_26__removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_26__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l___private_Lean_Elab_Inductive_26__removeUnused___closed__1;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l_List_forM___main___at___private_Lean_Elab_Inductive_25__collectUsed___spec__2(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_removeUnused(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Inductive_26__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_26__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_27__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_11 = l___private_Lean_Elab_Inductive_26__removeUnused(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_apply_1(x_3, x_17);
x_19 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_7__elabBinderViews___main___spec__3___rarg(x_15, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_27__withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_27__withUsed___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_27__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_27__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_19);
x_21 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_free_object(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
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
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_38 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_41);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_free_object(x_2);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_60 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
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
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
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
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_13, 2, x_23);
lean_ctor_set(x_13, 1, x_20);
x_25 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_2, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_free_object(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
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
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
x_46 = lean_ctor_get(x_13, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_47 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_50 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_53);
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_free_object(x_2);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
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
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_48);
lean_dec(x_44);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_65 = x_50;
} else {
 lean_dec_ref(x_50);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_46);
lean_dec(x_44);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_69 = x_47;
} else {
 lean_dec_ref(x_47);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_2);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_77 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_80 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 3, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_81);
x_84 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_83);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_96 = x_80;
} else {
 lean_dec_ref(x_80);
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
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_77, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_77, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_100 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
}
}
lean_object* l___private_Lean_Elab_Inductive_28__updateParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_28__updateParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_28__updateParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_CollectLevelParams_main___main(x_5, x_1);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_CollectLevelParams_main___main(x_5, x_1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__1(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1;
x_3 = l_List_foldl___main___at___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___spec__2(x_2, x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_11 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_12 = l_Lean_Elab_Command_InductiveView_inhabited;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_array_get(x_14, x_2, x_11);
lean_dec(x_11);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_3);
x_17 = l_Lean_mkConst(x_16, x_3);
x_18 = l_Std_HashMapImp_insert___at___private_Lean_MetavarContext_2__visit___spec__3(x_6, x_15, x_17);
x_5 = x_10;
x_6 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_30__mkIndFVar2Const(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(x_3);
x_5 = lean_array_get_size(x_1);
x_6 = l_Std_HashMap_inhabited___closed__1;
lean_inc(x_5);
x_7 = l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1(x_1, x_2, x_4, x_5, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_30__mkIndFVar2Const___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_30__mkIndFVar2Const___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_30__mkIndFVar2Const(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_161; lean_object* x_162; size_t x_163; uint8_t x_164; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_161 = lean_ctor_get(x_6, 0);
lean_inc(x_161);
x_162 = lean_array_uget(x_161, x_8);
x_163 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_164 = x_163 == x_7;
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = l_Lean_Expr_isFVar(x_5);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec(x_161);
x_166 = lean_box(0);
x_9 = x_166;
goto block_160;
}
else
{
lean_object* x_167; 
x_167 = l_Std_HashMapImp_find_x3f___at___private_Lean_MetavarContext_2__visit___spec__1(x_2, x_5);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
lean_dec(x_161);
x_168 = lean_box(0);
x_9 = x_168;
goto block_160;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Array_extract___rarg(x_3, x_170, x_1);
x_172 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_171, x_171, x_170, x_169);
lean_dec(x_171);
x_173 = lean_array_uset(x_161, x_8, x_5);
x_174 = lean_ctor_get(x_6, 1);
lean_inc(x_174);
lean_dec(x_6);
lean_inc(x_172);
x_175 = lean_array_uset(x_174, x_8, x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_161);
lean_dec(x_5);
x_178 = lean_ctor_get(x_6, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_8);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_6);
return x_180;
}
block_160:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_10, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_5);
x_20 = lean_array_uset(x_19, x_8, x_5);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_expr_update_app(x_5, x_13, x_17);
lean_inc(x_22);
x_23 = lean_array_uset(x_21, x_8, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_inc(x_5);
x_28 = lean_array_uset(x_27, x_8, x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_expr_update_app(x_5, x_13, x_25);
lean_inc(x_30);
x_31 = lean_array_uset(x_29, x_8, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_37 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_34, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_35, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_inc(x_5);
x_45 = lean_array_uset(x_44, x_8, x_5);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = (uint8_t)((x_36 << 24) >> 61);
x_48 = lean_expr_update_lambda(x_5, x_47, x_38, x_42);
lean_inc(x_48);
x_49 = lean_array_uset(x_46, x_8, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_inc(x_5);
x_54 = lean_array_uset(x_53, x_8, x_5);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = (uint8_t)((x_36 << 24) >> 61);
x_57 = lean_expr_update_lambda(x_5, x_56, x_38, x_51);
lean_inc(x_57);
x_58 = lean_array_uset(x_55, x_8, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
case 7:
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_64 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_62, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_5);
x_72 = lean_array_uset(x_71, x_8, x_5);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_63 << 24) >> 61);
x_75 = lean_expr_update_forall(x_5, x_74, x_65, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_8, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_67, 1, x_77);
lean_ctor_set(x_67, 0, x_75);
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_inc(x_5);
x_81 = lean_array_uset(x_80, x_8, x_5);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = (uint8_t)((x_63 << 24) >> 61);
x_84 = lean_expr_update_forall(x_5, x_83, x_65, x_78);
lean_inc(x_84);
x_85 = lean_array_uset(x_82, x_8, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
case 8:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_inc(x_90);
x_91 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_88, x_6);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_89, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_90, x_96);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_inc(x_5);
x_102 = lean_array_uset(x_101, x_8, x_5);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_expr_update_let(x_5, x_92, x_95, x_99);
lean_inc(x_104);
x_105 = lean_array_uset(x_103, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_97, 1, x_106);
lean_ctor_set(x_97, 0, x_104);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_97, 0);
x_108 = lean_ctor_get(x_97, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_inc(x_5);
x_110 = lean_array_uset(x_109, x_8, x_5);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_expr_update_let(x_5, x_92, x_95, x_107);
lean_inc(x_112);
x_113 = lean_array_uset(x_111, x_8, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
x_117 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_116, x_6);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_inc(x_5);
x_122 = lean_array_uset(x_121, x_8, x_5);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_expr_update_mdata(x_5, x_119);
lean_inc(x_124);
x_125 = lean_array_uset(x_123, x_8, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_117, 1, x_126);
lean_ctor_set(x_117, 0, x_124);
return x_117;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_117, 0);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_117);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_inc(x_5);
x_130 = lean_array_uset(x_129, x_8, x_5);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_expr_update_mdata(x_5, x_127);
lean_inc(x_132);
x_133 = lean_array_uset(x_131, x_8, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_5, 2);
lean_inc(x_136);
x_137 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_136, x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_inc(x_5);
x_142 = lean_array_uset(x_141, x_8, x_5);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_expr_update_proj(x_5, x_139);
lean_inc(x_144);
x_145 = lean_array_uset(x_143, x_8, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_137, 1, x_146);
lean_ctor_set(x_137, 0, x_144);
return x_137;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_137, 0);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_137);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_inc(x_5);
x_150 = lean_array_uset(x_149, x_8, x_5);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_expr_update_proj(x_5, x_147);
lean_inc(x_152);
x_153 = lean_array_uset(x_151, x_8, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
case 12:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_5);
x_156 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__4;
x_157 = l_unreachable_x21___rarg(x_156);
x_158 = lean_apply_1(x_157, x_6);
return x_158;
}
default: 
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
}
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_7__getResultingType___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 8192;
x_13 = l_Lean_Expr_ReplaceImpl_initCache;
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_12, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1___boxed), 11, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_4);
x_17 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2___rarg(x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_2);
x_30 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1___boxed), 11, 2);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_4);
x_31 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__2___rarg(x_28, x_29, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
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
lean_dec(x_27);
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_7(x_11, lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3), 12, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
x_16 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__3), 8, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_4);
x_17 = lean_apply_9(x_8, lean_box(0), lean_box(0), x_15, x_16, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_7(x_15, lean_box(0), x_13, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__2), 11, 6);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_1);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_6);
lean_closure_set(x_20, 5, x_7);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__4), 14, 8);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_19);
x_22 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_20, x_21, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3(x_2, x_3, x_4, x_5, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 2, x_19);
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
lean_ctor_set(x_1, 2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_15);
lean_dec(x_14);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3(x_2, x_3, x_4, x_5, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_27);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4), 12, 7);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
x_16 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__3), 8, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_4);
x_17 = lean_apply_9(x_8, lean_box(0), lean_box(0), x_15, x_16, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_7(x_15, lean_box(0), x_13, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__1), 12, 7);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4___lambda__2), 14, 8);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_19);
x_22 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_20, x_21, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Elab_Inductive_30__mkIndFVar2Const(x_1, x_2, x_3);
x_15 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_16 = l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__4(x_4, x_5, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___main___at___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(x_4, x_8, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 7);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1(x_7, x_8, x_9, x_4);
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_32__mkCtor2InferMod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_HashMap_inhabited___closed__1;
x_4 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_32__mkCtor2InferMod___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_32__mkCtor2InferMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_32__mkCtor2InferMod(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_HashMap_find_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(162u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Std_PersistentHashMap_find_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_8);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Bool_Inhabited;
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1;
x_15 = lean_box(x_13);
x_16 = lean_panic_fn(x_15, x_14);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_18);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_20);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; 
x_24 = 1;
x_25 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_24);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 0;
x_27 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_26);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_28);
x_32 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = l_Bool_Inhabited;
x_34 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1;
x_35 = lean_box(x_33);
x_36 = lean_panic_fn(x_35, x_34);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_40);
return x_3;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 0;
x_42 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_43);
return x_3;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = 1;
x_47 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_48);
return x_3;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_49 = 0;
x_50 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_29);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_53);
x_58 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_54);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Bool_Inhabited;
x_60 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1;
x_61 = lean_box(x_59);
x_62 = lean_panic_fn(x_61, x_60);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = 1;
x_65 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_64);
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = 0;
x_69 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_68);
if (lean_is_scalar(x_56)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_56;
}
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_57);
return x_71;
}
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = 1;
x_75 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_74);
if (lean_is_scalar(x_56)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_56;
}
lean_ctor_set(x_76, 0, x_54);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_57);
return x_77;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = 0;
x_79 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_78);
if (lean_is_scalar(x_56)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_56;
}
lean_ctor_set(x_80, 0, x_54);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_57);
return x_81;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_9);
lean_ctor_set(x_6, 2, x_10);
x_11 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_16 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(x_1, x_2, x_12);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 3, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(x_1, x_2, x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_33__applyInferMod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Inductive_32__mkCtor2InferMod(x_1);
x_5 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(x_2, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_33__applyInferMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_33__applyInferMod(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_6, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_77; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_24 = lean_array_fget(x_5, x_6);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
lean_dec(x_24);
x_94 = lean_st_ref_take(x_12, x_13);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_mk_rec_on(x_98, x_25);
lean_ctor_set(x_95, 0, x_99);
x_100 = lean_st_ref_set(x_12, x_95, x_96);
if (x_3 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_77 = x_101;
goto block_93;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_take(x_12, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_mk_cases_on(x_107, x_25);
lean_ctor_set(x_104, 0, x_108);
x_109 = lean_st_ref_set(x_12, x_104, x_105);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_77 = x_110;
goto block_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_104, 0);
x_112 = lean_ctor_get(x_104, 1);
x_113 = lean_ctor_get(x_104, 2);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_104);
x_114 = lean_mk_cases_on(x_111, x_25);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set(x_115, 2, x_113);
x_116 = lean_st_ref_set(x_12, x_115, x_105);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_77 = x_117;
goto block_93;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_95, 0);
x_119 = lean_ctor_get(x_95, 1);
x_120 = lean_ctor_get(x_95, 2);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_95);
x_121 = lean_mk_rec_on(x_118, x_25);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_120);
x_123 = lean_st_ref_set(x_12, x_122, x_96);
if (x_3 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_77 = x_124;
goto block_93;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_st_ref_take(x_12, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 2);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
x_133 = lean_mk_cases_on(x_129, x_25);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_131);
x_135 = lean_st_ref_set(x_12, x_134, x_128);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_77 = x_136;
goto block_93;
}
}
block_76:
{
uint8_t x_27; 
if (x_3 == 0)
{
uint8_t x_75; 
x_75 = 0;
x_27 = x_75;
goto block_74;
}
else
{
x_27 = x_4;
goto block_74;
}
block_74:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_72; 
x_72 = 0;
x_28 = x_72;
goto block_71;
}
else
{
uint8_t x_73; 
x_73 = 1;
x_28 = x_73;
goto block_71;
}
block_71:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_26;
goto block_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_st_ref_take(x_12, x_26);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_mk_below(x_60, x_25);
lean_ctor_set(x_57, 0, x_61);
x_62 = lean_st_ref_set(x_12, x_57, x_58);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_29 = x_63;
goto block_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
x_66 = lean_ctor_get(x_57, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_67 = lean_mk_below(x_64, x_25);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_66);
x_69 = lean_st_ref_set(x_12, x_68, x_58);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_29 = x_70;
goto block_55;
}
}
block_55:
{
if (x_28 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_14 = x_31;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_take(x_12, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_mk_ibelow(x_36, x_25);
lean_dec(x_25);
lean_ctor_set(x_33, 0, x_37);
x_38 = lean_st_ref_set(x_12, x_33, x_34);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
x_14 = x_38;
goto block_19;
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
x_14 = x_44;
goto block_19;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_48 = lean_mk_ibelow(x_45, x_25);
lean_dec(x_25);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_st_ref_set(x_12, x_49, x_34);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_14 = x_54;
goto block_19;
}
}
}
}
}
}
block_93:
{
if (x_3 == 0)
{
x_26 = x_77;
goto block_76;
}
else
{
if (x_1 == 0)
{
x_26 = x_77;
goto block_76;
}
else
{
if (x_2 == 0)
{
x_26 = x_77;
goto block_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_st_ref_take(x_12, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_mk_no_confusion(x_82, x_25);
lean_ctor_set(x_79, 0, x_83);
x_84 = lean_st_ref_set(x_12, x_79, x_80);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_26 = x_85;
goto block_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
x_88 = lean_ctor_get(x_79, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_89 = lean_mk_no_confusion(x_86, x_25);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_88);
x_91 = lean_st_ref_set(x_12, x_90, x_80);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_26 = x_92;
goto block_76;
}
}
}
}
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_6 = x_17;
x_13 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_fget(x_3, x_4);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
if (x_1 == 0)
{
uint8_t x_65; 
x_65 = 0;
x_18 = x_65;
goto block_64;
}
else
{
x_18 = x_2;
goto block_64;
}
block_64:
{
uint8_t x_19; 
if (x_18 == 0)
{
uint8_t x_62; 
x_62 = 0;
x_19 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 1;
x_19 = x_63;
goto block_61;
}
block_61:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_11;
goto block_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_st_ref_take(x_10, x_11);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_mk_brec_on(x_50, x_17);
lean_ctor_set(x_47, 0, x_51);
x_52 = lean_st_ref_set(x_10, x_47, x_48);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_20 = x_53;
goto block_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
x_56 = lean_ctor_get(x_47, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_57 = lean_mk_brec_on(x_54, x_17);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
x_59 = lean_st_ref_set(x_10, x_58, x_48);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_20 = x_60;
goto block_45;
}
}
block_45:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_4 = x_22;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_st_ref_take(x_10, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_mk_binduction_on(x_28, x_17);
lean_dec(x_17);
lean_ctor_set(x_25, 0, x_29);
x_30 = lean_st_ref_set(x_10, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_4, x_32);
lean_dec(x_4);
x_4 = x_33;
x_11 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
x_37 = lean_ctor_get(x_25, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_38 = lean_mk_binduction_on(x_35, x_17);
lean_dec(x_17);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_st_ref_set(x_10, x_39, x_26);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_4, x_42);
lean_dec(x_4);
x_4 = x_43;
x_11 = x_41;
goto _start;
}
}
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Environment_contains(x_12, x_13);
x_15 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_12);
x_16 = l_Lean_Environment_contains(x_12, x_15);
x_17 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_inc(x_12);
x_18 = l_Lean_Environment_contains(x_12, x_17);
x_19 = l_Lean_prodToExpr___rarg___lambda__1___closed__2;
x_20 = l_Lean_Environment_contains(x_12, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(x_14, x_16, x_18, x_20, x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(x_18, x_20, x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(x_14, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_18;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_nat_sub(x_4, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_3, x_19);
x_22 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_23 = lean_array_get(x_22, x_1, x_19);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 4);
lean_inc(x_24);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_2);
x_25 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_Inductive_16__elabCtors(x_21, x_2, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_29);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
x_5 = x_17;
x_6 = x_34;
x_13 = x_30;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
}
}
lean_object* l_Lean_Elab_applyAttributes___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_1, x_3, x_2, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_array_fget(x_5, x_6);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
x_24 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_19, x_22, x_21, x_23, x_11, x_12, x_13);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_6, x_26);
lean_dec(x_6);
x_6 = x_27;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_56; 
x_17 = lean_array_get_size(x_9);
x_18 = lean_nat_add(x_17, x_1);
lean_inc(x_12);
lean_inc(x_10);
x_56 = l_List_mapM___main___at___private_Lean_Elab_Inductive_28__updateParams___spec__2(x_9, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_10);
x_59 = l___private_Lean_Elab_Inductive_18__levelMVarToParam(x_57, x_10, x_11, x_12, x_13, x_14, x_15, x_58);
if (x_8 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_19 = x_60;
x_20 = x_61;
goto block_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_64 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse(x_18, x_62, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_19 = x_65;
x_20 = x_66;
goto block_55;
}
else
{
uint8_t x_67; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_56);
if (x_71 == 0)
{
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
block_55:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_19);
x_21 = l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive(x_19);
x_22 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_18);
lean_inc(x_27);
x_28 = l___private_Lean_Elab_Inductive_31__replaceIndFVarsWithConsts(x_4, x_5, x_27, x_17, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Elab_Inductive_33__applyInferMod(x_4, x_18, x_29);
x_32 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_6);
lean_inc(x_10);
lean_inc(x_32);
x_33 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_10);
x_35 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions(x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_MonadCacheT_MonadLift___closed__1;
x_40 = l_ReaderT_MonadLift___closed__1;
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3(x_39, x_40, x_39, x_40, x_4, x_41, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
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
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_box(0);
x_18 = lean_array_get_size(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_19 = l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1(x_2, x_7, x_8, x_18, x_18, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_reverse___rarg(x_20);
x_23 = 0;
x_24 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_23, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_27 = l___private_Lean_Elab_Inductive_19__getResultingUniverse(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
x_30 = l_Lean_Elab_Command_shouldInferResultUniverse(x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(x_5);
lean_inc(x_22);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1___boxed), 16, 8);
lean_closure_set(x_34, 0, x_16);
lean_closure_set(x_34, 1, x_3);
lean_closure_set(x_34, 2, x_4);
lean_closure_set(x_34, 3, x_1);
lean_closure_set(x_34, 4, x_8);
lean_closure_set(x_34, 5, x_33);
lean_closure_set(x_34, 6, x_22);
lean_closure_set(x_34, 7, x_31);
x_35 = l___private_Lean_Elab_Inductive_27__withUsed___rarg(x_6, x_22, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_4);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2___boxed), 15, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_5);
x_16 = l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(x_6, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Elab_Command_InductiveView_inhabited;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_2, x_11);
x_13 = l_Lean_Elab_Term_getLevelNames(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_Inductive_4__checkLevelNames(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_inc(x_2);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_12__elabHeader), 8, 1);
lean_closure_set(x_22, 0, x_2);
x_23 = lean_box(x_20);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3___boxed), 13, 5);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_18);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_1);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_7, 3);
x_28 = l_Lean_replaceRef(x_21, x_27);
lean_dec(x_21);
x_29 = l_Lean_replaceRef(x_28, x_27);
lean_dec(x_28);
x_30 = l_Lean_replaceRef(x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
lean_ctor_set(x_7, 3, x_30);
x_31 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_ctor_get(x_7, 2);
x_35 = lean_ctor_get(x_7, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_36 = l_Lean_replaceRef(x_21, x_35);
lean_dec(x_21);
x_37 = l_Lean_replaceRef(x_36, x_35);
lean_dec(x_36);
x_38 = l_Lean_replaceRef(x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_25, x_3, x_4, x_5, x_6, x_39, x_8, x_17);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_applyAttributes___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_applyAttributes___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_35__mkInductiveDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__2(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_Inductive_35__mkInductiveDecl___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
x_16 = l___private_Lean_Elab_Inductive_35__mkInductiveDecl(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_21 = l_Lean_replaceRef(x_1, x_20);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
x_25 = l___private_Lean_Elab_Inductive_35__mkInductiveDecl(x_3, x_2, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Lean_Elab_Command_InductiveView_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed), 10, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Command_4__getVarDecls(x_13);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_11);
x_17 = l_Lean_Elab_Command_liftTermElabM___rarg(x_10, x_16, x_2, x_3, x_14);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabInductiveViews___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabInductiveViews(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_Constructions(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Inductive(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Constructions(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__4 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__4);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__5 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__5);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__6 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__6);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__7 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__7);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__8 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__8);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__9 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__9);
l_Lean_Elab_Command_checkValidCtorModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___closed__4 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__4);
l_Lean_Elab_Command_checkValidCtorModifier___closed__5 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__5);
l_Lean_Elab_Command_checkValidCtorModifier___closed__6 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__6);
l_Lean_Elab_Command_checkValidCtorModifier___closed__7 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__7);
l_Lean_Elab_Command_checkValidCtorModifier___closed__8 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__8);
l_Lean_Elab_Command_checkValidCtorModifier___closed__9 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__9);
l_Lean_Elab_Command_checkValidCtorModifier___closed__10 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__10);
l_Lean_Elab_Command_checkValidCtorModifier___closed__11 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__11);
l_Lean_Elab_Command_checkValidCtorModifier___closed__12 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__12);
l_Lean_Elab_Command_CtorView_inhabited___closed__1 = _init_l_Lean_Elab_Command_CtorView_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited___closed__1);
l_Lean_Elab_Command_CtorView_inhabited___closed__2 = _init_l_Lean_Elab_Command_CtorView_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited___closed__2);
l_Lean_Elab_Command_CtorView_inhabited = _init_l_Lean_Elab_Command_CtorView_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited);
l_Lean_Elab_Command_InductiveView_inhabited___closed__1 = _init_l_Lean_Elab_Command_InductiveView_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_InductiveView_inhabited___closed__1);
l_Lean_Elab_Command_InductiveView_inhabited = _init_l_Lean_Elab_Command_InductiveView_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_InductiveView_inhabited);
l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1 = _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1);
l_Lean_Elab_Command_ElabHeaderResult_inhabited = _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_ElabHeaderResult_inhabited);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3);
l___private_Lean_Elab_Inductive_7__getResultingType___closed__1 = _init_l___private_Lean_Elab_Inductive_7__getResultingType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_7__getResultingType___closed__1);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___lambda__1___closed__3);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__1);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__2);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___closed__3);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6);
l_Lean_Elab_Command_tmpIndParam___closed__1 = _init_l_Lean_Elab_Command_tmpIndParam___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__1);
l_Lean_Elab_Command_tmpIndParam___closed__2 = _init_l_Lean_Elab_Command_tmpIndParam___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__2);
l_Lean_Elab_Command_tmpIndParam___closed__3 = _init_l_Lean_Elab_Command_tmpIndParam___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__3);
l_Lean_Elab_Command_tmpIndParam = _init_l_Lean_Elab_Command_tmpIndParam();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__1 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__1);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__2 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__2);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__3 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__3);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__4 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__4);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__5 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__5);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__6 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__6);
l_Lean_Elab_Command_accLevelAtCtor___main___closed__1 = _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___main___closed__1);
l_Lean_Elab_Command_accLevelAtCtor___main___closed__2 = _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___main___closed__2);
l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2);
l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1 = _init_l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__4___closed__1);
l___private_Lean_Elab_Inductive_26__removeUnused___closed__1 = _init_l___private_Lean_Elab_Inductive_26__removeUnused___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_26__removeUnused___closed__1);
l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1 = _init_l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1);
l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1 = _init_l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at___private_Lean_Elab_Inductive_33__applyInferMod___spec__1___closed__1);
l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1 = _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1);
l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2 = _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
