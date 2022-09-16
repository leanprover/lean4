// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: Init Lean.Util.Recognizers Lean.Meta.Instances Lean.Compiler.InlineAttrs Lean.Compiler.Specialize Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Stage1 Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.AlphaEqv
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
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_subst___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_Config_etaPoly___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6;
static lean_object* l_Lean_Compiler_LCNF_simp___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5;
lean_object* l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_visited___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_Config_implementedBy___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Compiler_implementedByAttr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1;
lean_object* l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDecls_go___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTemplateLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Context_discrCtorMap___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_inline___default;
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedConfig;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs(lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(uint8_t);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Config_smallThreshold___default;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_has_specialize_attribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go(lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTemplateLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Compiler_LCNF_attachCodeDecls_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getStage1Decl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_State_simplified___default;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstructorApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_Config_inlinePartial___default;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1;
lean_object* l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_collectLocalDecls_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2;
lean_object* l_Lean_Compiler_LCNF_getFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173_(uint8_t, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___boxed(lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_used___default;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default;
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
static lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Context_config___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_4 = l_Lean_BinderInfo_isInstImplicit(x_3);
if (x_4 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_hasLocalInst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTemplateLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = l_Lean_Compiler_LCNF_hasLocalInst(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_7);
x_8 = l_Lean_Meta_isInstance(x_7, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 0;
lean_inc(x_7);
x_21 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_15, x_20, x_7);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_has_specialize_attribute(x_19, x_7);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_7);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 0;
lean_inc(x_7);
x_33 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_15, x_32, x_7);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_has_specialize_attribute(x_31, x_7);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_7);
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
lean_dec(x_45);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_8, 0, x_47);
return x_8;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_dec(x_8);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isTemplateLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_isTemplateLike(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.FunDeclInfo.once", 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.FunDeclInfo.many", 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.FunDeclInfo.mustInline", 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
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
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ↦ ", 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Compiler_LCNF_getBinderName(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_13, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unbox(x_11);
lean_dec(x_11);
x_26 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173_(x_25, x_24);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
x_1 = x_9;
x_2 = x_29;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Std_HashMap_toList___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__1(x_1);
x_7 = lean_box(0);
x_8 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4(x_6, x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(x_2);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_name_eq(x_12, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(x_1, x_2, x_14);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = lean_box(x_2);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_box(x_3);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
x_17 = lean_array_uset(x_6, x_10, x_16);
x_18 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_19 = lean_nat_dec_le(x_18, x_7);
lean_dec(x_7);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__5(x_14, x_17);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_21 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(x_2, x_3, x_11);
x_22 = lean_array_uset(x_6, x_10, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_modn(x_27, x_25);
x_29 = lean_array_uget(x_24, x_28);
x_30 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(x_2, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_23, x_31);
lean_dec(x_23);
x_33 = lean_box(x_3);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
x_35 = lean_array_uset(x_24, x_28, x_34);
x_36 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_32);
x_37 = lean_nat_dec_le(x_36, x_25);
lean_dec(x_25);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__5(x_32, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_40 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(x_2, x_3, x_29);
x_41 = lean_array_uset(x_24, x_28, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_1, x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_1, x_2, x_7);
return x_8;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 2;
x_4 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(x_1, x_7);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(x_1, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_usize_modn(x_7, x_5);
lean_dec(x_5);
x_9 = lean_array_uget(x_4, x_8);
x_10 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__4(x_2, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(x_2, x_9);
x_17 = lean_array_uset(x_4, x_8, x_16);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(x_2, x_9);
x_21 = lean_array_uset(x_4, x_8, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1(x_1, x_2);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_1, x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_6);
x_7 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_6, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_6, x_2, x_3, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_20;
x_5 = x_18;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_29 = x_8;
} else {
 lean_dec_ref(x_8);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
case 10:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_1 = x_32;
goto _start;
}
default: 
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_7, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_1 = x_16;
x_2 = x_17;
x_6 = x_14;
goto _start;
}
}
case 10:
{
if (x_2 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 1;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
default: 
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Compiler_LCNF_Simp_findExpr(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Config_smallThreshold___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_Config_etaPoly___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_Config_inlinePartial___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_Config_implementedBy___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_discrCtorMap___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_used___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_State_simplified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_visited___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_inline___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = l_Lean_Compiler_LCNF_Simp_findExpr(x_1, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
x_15 = l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(x_14, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
return x_9;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
x_20 = l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(x_19, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_findCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(x_20, x_2, x_3, x_4, x_5, x_6, x_11);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = lean_environment_find(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_1, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(x_33, x_2, x_3, x_4, x_5, x_6, x_24);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a constructor", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 6)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_const___override(x_1, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4(x_23, x_2, x_3, x_4, x_5, x_6, x_16);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_Compiler_LCNF_erasedExpr;
x_18 = l_Lean_Expr_app___override(x_5, x_17);
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_fvar___override(x_14);
x_16 = l_Lean_Expr_app___override(x_4, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__8(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_2, x_14);
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5(x_16, x_17, x_16, x_18, x_15, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_3);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6(x_3, x_23, x_24, x_20, x_5, x_6, x_7, x_8, x_9, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 2);
x_30 = l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(x_29, x_1, x_26);
lean_ctor_set(x_5, 2, x_30);
x_31 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
x_34 = lean_ctor_get(x_5, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_35 = l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(x_34, x_1, x_26);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_apply_6(x_4, x_36, x_6, x_7, x_8, x_9, x_27);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__6(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_12 = 1;
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_12);
x_13 = lean_st_ref_set(x_1, x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
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
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_9, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
x_28 = lean_st_ref_set(x_1, x_27, x_10);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_markSimplified(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 3, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_26, x_29);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_25);
x_32 = lean_st_ref_set(x_1, x_31, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incVisited(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 4, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_27, x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_25);
x_32 = lean_st_ref_set(x_1, x_31, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_incInline___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInline(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 5, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_25);
x_32 = lean_st_ref_set(x_1, x_31, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = 2;
x_16 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_14, x_1, x_15);
lean_ctor_set(x_11, 2, x_16);
x_17 = lean_st_ref_set(x_3, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_28 = lean_ctor_get(x_11, 3);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_ctor_get(x_11, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_31 = 2;
x_32 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_26, x_1, x_31);
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_27);
x_34 = lean_st_ref_set(x_3, x_33, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(x_14, x_1);
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_30 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(x_25, x_1);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_26);
x_32 = lean_st_ref_set(x_3, x_31, x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_addFunOcc(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_3);
x_14 = l_Lean_Compiler_LCNF_AltCore_getCode(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_2, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(x_14, x_5, x_6, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_10;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_Simp_addFunOcc(x_21, x_3, x_4, x_5, x_6, x_7, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_10;
x_8 = x_23;
goto _start;
}
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(x_25, x_1, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_31, x_3, x_4, x_5, x_6, x_7, x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(x_29, x_1, x_30, x_33, x_3, x_4, x_5, x_6, x_7, x_34);
return x_35;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_ctor_get(x_36, 4);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_2 = x_37;
x_8 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
case 3:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_Compiler_LCNF_getFunDecl(x_46, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_Simp_addFunOcc(x_50, x_3, x_4, x_5, x_6, x_7, x_49);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 4:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_array_get_size(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_8);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_58, x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_68 = lean_box(0);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1(x_1, x_57, x_66, x_67, x_68, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_57);
return x_69;
}
}
}
default: 
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_8);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_st_ref_get(x_7, x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_4, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_1, x_3, x_4, x_5, x_6, x_7, x_26);
lean_inc(x_1);
x_29 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_27, x_1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_4);
x_31 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_7, x_33);
lean_dec(x_7);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_4, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_37, 2);
x_41 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_40, x_1, x_29);
lean_ctor_set(x_37, 2, x_41);
x_42 = lean_st_ref_set(x_4, x_37, x_38);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_42, 0, x_46);
x_9 = x_42;
goto block_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_9 = x_50;
goto block_21;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get_uint8(x_37, sizeof(void*)*6);
x_55 = lean_ctor_get(x_37, 3);
x_56 = lean_ctor_get(x_37, 4);
x_57 = lean_ctor_get(x_37, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_58 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_53, x_1, x_29);
x_59 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_54);
x_60 = lean_st_ref_set(x_4, x_59, x_38);
lean_dec(x_4);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_32);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
x_9 = x_65;
goto block_21;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_31, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_31, 1);
lean_inc(x_67);
lean_dec(x_31);
x_68 = lean_st_ref_get(x_7, x_67);
lean_dec(x_7);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_4, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_71, 2);
x_75 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_74, x_1, x_29);
lean_ctor_set(x_71, 2, x_75);
x_76 = lean_st_ref_set(x_4, x_71, x_72);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_66);
x_9 = x_76;
goto block_21;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_79);
x_9 = x_80;
goto block_21;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_71, 0);
x_82 = lean_ctor_get(x_71, 1);
x_83 = lean_ctor_get(x_71, 2);
x_84 = lean_ctor_get_uint8(x_71, sizeof(void*)*6);
x_85 = lean_ctor_get(x_71, 3);
x_86 = lean_ctor_get(x_71, 4);
x_87 = lean_ctor_get(x_71, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_71);
x_88 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_83, x_1, x_29);
x_89 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*6, x_84);
x_90 = lean_st_ref_set(x_4, x_89, x_72);
lean_dec(x_4);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_66);
lean_ctor_set(x_93, 1, x_91);
x_9 = x_93;
goto block_21;
}
}
block_21:
{
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 1)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_17);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = l_Lean_Compiler_LCNF_Code_sizeLe(x_8, x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isSmall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_13 = l_Lean_Compiler_LCNF_Simp_isSmall(x_1, x_2, x_3, x_4, x_5, x_6, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findIdx_x3f_loop___rarg(x_5, x_6, x_7, x_8, lean_box(0));
return x_9;
}
case 5:
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
case 6:
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_12 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_10, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 5);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_22);
x_29 = lean_st_ref_set(x_7, x_28, x_18);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get(x_1, 4);
x_34 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_2);
x_35 = lean_mk_array(x_2, x_34);
x_36 = lean_nat_sub(x_2, x_26);
lean_dec(x_2);
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_35, x_36);
x_38 = 1;
lean_inc(x_33);
lean_inc(x_32);
x_39 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_4);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get(x_1, 4);
x_44 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_2);
x_45 = lean_mk_array(x_2, x_44);
x_46 = lean_nat_sub(x_2, x_26);
lean_dec(x_2);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_45, x_46);
x_48 = 1;
lean_inc(x_43);
lean_inc(x_42);
x_49 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (x_5 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_23, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_26, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_1, x_2);
x_14 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_1, x_2);
x_15 = l_Lean_Compiler_LCNF_Simp_incInline___rarg(x_8, x_9, x_10, x_11, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_3);
x_19 = lean_mk_array(x_3, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_3, x_20);
lean_dec(x_3);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_19, x_21);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_3);
x_28 = lean_mk_array(x_3, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_3, x_29);
lean_dec(x_3);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_28, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_5);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_nat_sub(x_1, x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_Expr_getRevArg_x21(x_3, x_14);
x_16 = l_Lean_Compiler_LCNF_Simp_findCtor(x_15, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_10, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isConstructorApp(x_23, x_17);
lean_dec(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_25 = lean_box(0);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_19);
x_26 = lean_box(0);
x_27 = lean_apply_7(x_4, x_26, x_6, x_7, x_8, x_9, x_10, x_22);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_isConstructorApp(x_30, x_17);
lean_dec(x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_apply_7(x_4, x_34, x_6, x_7, x_8, x_9, x_10, x_29);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_7);
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_14, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3___boxed), 12, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
x_17 = l_Lean_Compiler_LCNF_Simp_isCasesOnParam_x3f(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_nat_dec_lt(x_20, x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(x_3, x_20, x_4, x_16, x_24, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_20);
lean_dec(x_3);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_dec(x_8);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_1, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
if (x_7 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = l_Lean_Compiler_LCNF_Decl_getArity(x_28);
x_30 = lean_nat_dec_lt(x_3, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(x_28, x_2, x_3, x_4, x_5, x_6, x_31, x_9, x_10, x_11, x_12, x_13, x_26);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
lean_dec(x_16);
x_36 = l_Lean_Compiler_LCNF_Decl_getArity(x_35);
x_37 = lean_nat_dec_lt(x_3, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(x_35, x_2, x_3, x_4, x_5, x_6, x_38, x_9, x_10, x_11, x_12, x_13, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_dec(x_15);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_box(0);
x_45 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(x_43, x_2, x_3, x_4, x_5, x_6, x_44, x_9, x_10, x_11, x_12, x_13, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(x_47, x_2, x_3, x_4, x_5, x_6, x_48, x_9, x_10, x_11, x_12, x_13, x_46);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_7);
x_14 = lean_st_ref_get(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 3;
lean_inc(x_1);
x_19 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_17, x_18, x_1);
x_20 = lean_st_ref_get(x_12, x_16);
if (x_6 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
lean_inc(x_1);
x_26 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_24, x_25, x_1);
if (x_26 == 0)
{
if (x_19 == 0)
{
lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_20);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_6, x_28, x_8, x_9, x_10, x_11, x_12, x_23);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_20);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_6, x_30, x_8, x_9, x_10, x_11, x_12, x_23);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 0;
lean_inc(x_1);
x_36 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_34, x_35, x_1);
if (x_36 == 0)
{
if (x_19 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_6, x_39, x_8, x_9, x_10, x_11, x_12, x_33);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_6, x_41, x_8, x_9, x_10, x_11, x_12, x_33);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_box(0);
x_45 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_6, x_44, x_8, x_9, x_10, x_11, x_12, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = l_Lean_Expr_getAppFn(x_1);
x_13 = 1;
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_Simp_findExpr(x_12, x_13, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 4)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_name_eq(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_14);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7(x_19, x_20, x_11, x_1, x_12, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_17);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = lean_name_eq(x_27, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7(x_27, x_28, x_11, x_1, x_12, x_2, x_31, x_4, x_5, x_6, x_7, x_8, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
lean_inc(x_12);
x_36 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(x_12, x_6, x_7, x_8, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_36, 1);
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_nat_dec_lt(x_10, x_11);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = lean_box(0);
lean_ctor_set(x_36, 0, x_49);
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_36);
x_50 = lean_box(0);
x_51 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_47, x_11, x_1, x_12, x_2, x_50, x_4, x_5, x_6, x_7, x_8, x_45);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_nat_dec_lt(x_10, x_11);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_53, x_11, x_1, x_12, x_2, x_57, x_4, x_5, x_6, x_7, x_8, x_52);
return x_58;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1;
x_9 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3;
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_box(0);
x_14 = lean_box(x_12);
x_15 = lean_apply_9(x_8, x_1, x_14, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_17 = 1;
x_18 = l_Lean_Compiler_LCNF_Simp_findExpr(x_16, x_17, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_box(x_17);
x_23 = lean_apply_9(x_8, x_19, x_22, x_21, x_2, x_3, x_4, x_5, x_6, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__6(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__7(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_15, x_1, x_2);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_4, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
x_28 = lean_ctor_get(x_12, 3);
x_29 = lean_ctor_get(x_12, 4);
x_30 = lean_ctor_get(x_12, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_31 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_24, x_1, x_2);
x_32 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_27);
x_33 = lean_st_ref_set(x_4, x_32, x_13);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
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
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_addSubst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Compiler_LCNF_AltCore_getCode(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 3:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 3);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_6, x_6);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_6);
x_14 = 0;
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1(x_5, x_15, x_16);
return x_17;
}
}
}
}
case 5:
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
case 6:
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
default: 
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
x_1 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_fget(x_17, x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_18, x_27);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_28);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_16, x_29, x_26);
lean_ctor_set(x_4, 1, x_30);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
lean_dec(x_15);
x_34 = lean_array_fget(x_17, x_18);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_18, x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_16, x_38, x_34);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_37);
x_40 = 1;
x_41 = lean_usize_add(x_3, x_40);
x_3 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_13);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; 
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
x_52 = lean_array_fget(x_45, x_46);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_46, x_53);
lean_dec(x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_47);
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_44, x_56, x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = 1;
x_60 = lean_usize_add(x_3, x_59);
x_3 = x_60;
x_4 = x_58;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_toSubarray___rarg(x_3, x_12, x_11);
x_14 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_17, x_18, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_Code_internalize(x_2, x_22, x_7, x_8, x_9, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_24);
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
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_uget(x_13, x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_replaceExprFVars(x_17, x_16, x_7, x_8, x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 0;
x_22 = l_Lean_Compiler_LCNF_mkAuxParam(x_19, x_21, x_7, x_8, x_9, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_array_push(x_15, x_23);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Expr_fvar___override(x_27);
x_29 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_16, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_30;
x_10 = x_24;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_f", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_11 = l_Array_toSubarray___rarg(x_8, x_10, x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
x_17 = 0;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_12, x_16, x_17, x_14, x_2, x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Array_toSubarray___rarg(x_12, x_9, x_15);
x_24 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_ctor_set(x_19, 0, x_24);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_23, x_26, x_28, x_19, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_Compiler_LCNF_Code_internalize(x_34, x_33, x_4, x_5, x_6, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_36);
x_39 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_38, x_36, x_2, x_3, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_42 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_32, x_36, x_41, x_4, x_5, x_6, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_dec(x_19);
x_48 = l_Array_toSubarray___rarg(x_12, x_9, x_15);
x_49 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_ctor_get(x_48, 2);
lean_inc(x_51);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_48, x_52, x_54, x_50, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Lean_Compiler_LCNF_Code_internalize(x_60, x_59, x_4, x_5, x_6, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_62);
x_65 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_64, x_62, x_2, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_58, x_62, x_67, x_4, x_5, x_6, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
x_19 = lean_ctor_get(x_6, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_st_ref_take(x_7, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_29 = 0;
x_30 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
lean_inc(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_PersistentArray_push___rarg(x_27, x_31);
lean_ctor_set(x_24, 3, x_32);
x_33 = lean_st_ref_set(x_7, x_24, x_25);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 4);
x_45 = lean_ctor_get(x_24, 5);
x_46 = lean_ctor_get(x_24, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_47 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_48 = 0;
x_49 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_22);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
lean_inc(x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_43, x_50);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_46);
x_53 = lean_st_ref_set(x_7, x_52, x_25);
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
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Expr_fvar___override(x_3);
x_10 = lean_array_push(x_2, x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1;
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_3, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 7, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_10);
x_17 = l_Lean_Compiler_LCNF_Code_bind(x_2, x_16, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
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
lean_dec(x_2);
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
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_replaceFVar(x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Expr_fvar___override(x_6);
x_14 = lean_array_get_size(x_5);
x_15 = l_Array_toSubarray___rarg(x_5, x_1, x_14);
x_16 = l_Array_ofSubarray___rarg(x_15);
x_17 = l_Lean_mkAppN(x_13, x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_17, x_18, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Lean_Compiler_LCNF_replaceFVar(x_3, x_4, x_22, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_2);
x_15 = lean_nat_dec_lt(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_4);
x_19 = l_Array_toSubarray___rarg(x_4, x_18, x_14);
x_20 = l_Array_ofSubarray___rarg(x_19);
x_21 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_22 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_16, x_17, x_20, x_21, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_74; uint8_t x_89; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_89 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_5, x_13);
if (x_89 == 0)
{
uint8_t x_90; 
lean_free_object(x_22);
x_90 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_24);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_26 = x_91;
goto block_73;
}
else
{
lean_object* x_92; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_92 = lean_box(0);
x_74 = x_92;
goto block_88;
}
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_eq(x_3, x_14);
if (x_93 == 0)
{
uint8_t x_94; 
lean_free_object(x_22);
x_94 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_24);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_26 = x_95;
goto block_73;
}
else
{
lean_object* x_96; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_96 = lean_box(0);
x_74 = x_96;
goto block_88;
}
}
else
{
lean_object* x_97; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_22, 0, x_97);
return x_22;
}
}
block_73:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_mkAppN(x_27, x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Compiler_LCNF_inferType(x_28, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Compiler_LCNF_mkAuxParam(x_30, x_21, x_9, x_10, x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_nat_dec_lt(x_14, x_3);
lean_dec(x_3);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_4);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Compiler_LCNF_replaceFVar(x_5, x_13, x_36, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_33, x_24, x_38, x_7, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_8);
lean_dec(x_7);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
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
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
x_46 = l_Lean_Expr_fvar___override(x_45);
x_47 = lean_array_get_size(x_4);
x_48 = l_Array_toSubarray___rarg(x_4, x_14, x_47);
x_49 = l_Array_ofSubarray___rarg(x_48);
x_50 = l_Lean_mkAppN(x_46, x_49);
x_51 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_50, x_51, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_56 = l_Lean_Compiler_LCNF_replaceFVar(x_5, x_13, x_55, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_33, x_24, x_59, x_7, x_8, x_9, x_10, x_11, x_58);
lean_dec(x_8);
lean_dec(x_7);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_53);
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
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
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_52);
if (x_65 == 0)
{
return x_52;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_52);
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
uint8_t x_69; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_29);
if (x_69 == 0)
{
return x_29;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_29, 0);
x_71 = lean_ctor_get(x_29, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_29);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_88:
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_74);
x_75 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 10, 5);
lean_closure_set(x_75, 0, x_14);
lean_closure_set(x_75, 1, x_3);
lean_closure_set(x_75, 2, x_5);
lean_closure_set(x_75, 3, x_13);
lean_closure_set(x_75, 4, x_4);
x_76 = l_Lean_Compiler_LCNF_Code_bind(x_24, x_75, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
return x_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_148; uint8_t x_161; 
x_98 = lean_ctor_get(x_22, 0);
x_99 = lean_ctor_get(x_22, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_22);
x_161 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_5, x_13);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_98);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_box(0);
x_100 = x_163;
goto block_147;
}
else
{
lean_object* x_164; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_164 = lean_box(0);
x_148 = x_164;
goto block_160;
}
}
else
{
uint8_t x_165; 
x_165 = lean_nat_dec_eq(x_3, x_14);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_98);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_box(0);
x_100 = x_167;
goto block_147;
}
else
{
lean_object* x_168; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_168 = lean_box(0);
x_148 = x_168;
goto block_160;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_98);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_99);
return x_170;
}
}
block_147:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
lean_dec(x_2);
x_102 = l_Lean_mkAppN(x_101, x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_103 = l_Lean_Compiler_LCNF_inferType(x_102, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Compiler_LCNF_mkAuxParam(x_104, x_21, x_9, x_10, x_11, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_nat_dec_lt(x_14, x_3);
lean_dec(x_3);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_14);
lean_dec(x_4);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_111 = l_Lean_Compiler_LCNF_replaceFVar(x_5, x_13, x_110, x_9, x_10, x_11, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_107, x_98, x_112, x_7, x_8, x_9, x_10, x_11, x_113);
lean_dec(x_8);
lean_dec(x_7);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_107);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
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
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_107, 0);
lean_inc(x_119);
x_120 = l_Lean_Expr_fvar___override(x_119);
x_121 = lean_array_get_size(x_4);
x_122 = l_Array_toSubarray___rarg(x_4, x_14, x_121);
x_123 = l_Array_ofSubarray___rarg(x_122);
x_124 = l_Lean_mkAppN(x_120, x_123);
x_125 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_126 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_124, x_125, x_9, x_10, x_11, x_108);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_130 = l_Lean_Compiler_LCNF_replaceFVar(x_5, x_13, x_129, x_9, x_10, x_11, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_107, x_98, x_133, x_7, x_8, x_9, x_10, x_11, x_132);
lean_dec(x_8);
lean_dec(x_7);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_127);
lean_dec(x_107);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_107);
lean_dec(x_98);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_126, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_141 = x_126;
} else {
 lean_dec_ref(x_126);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = lean_ctor_get(x_103, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_103, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_145 = x_103;
} else {
 lean_dec_ref(x_103);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
block_160:
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_148);
x_149 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 10, 5);
lean_closure_set(x_149, 0, x_14);
lean_closure_set(x_149, 1, x_3);
lean_closure_set(x_149, 2, x_5);
lean_closure_set(x_149, 3, x_13);
lean_closure_set(x_149, 4, x_4);
x_150 = l_Lean_Compiler_LCNF_Code_bind(x_98, x_149, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_151);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
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
uint8_t x_171; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_22);
if (x_171 == 0)
{
return x_22;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_22, 0);
x_173 = lean_ctor_get(x_22, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_22);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_175 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = l_Lean_Expr_fvar___override(x_178);
x_180 = l_Lean_Compiler_LCNF_Simp_addSubst(x_13, x_179, x_7, x_8, x_9, x_10, x_11, x_177);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_176);
lean_ctor_set(x_183, 1, x_5);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
lean_dec(x_180);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_5);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
}
else
{
uint8_t x_189; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_189 = !lean_is_exclusive(x_175);
if (x_189 == 0)
{
return x_175;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_175, 0);
x_191 = lean_ctor_get(x_175, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_175);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inlining ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_5, x_6, x_7, x_8, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 3);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_26 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_1, x_20, x_24, x_23, x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_10);
x_34 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_25, x_37, x_4, x_5, x_6, x_7, x_8, x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_1, x_20, x_24, x_23, x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_dec(x_1);
x_14 = 0;
x_15 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_12, x_13, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
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
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_5, x_6, x_7, x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
lean_inc(x_18);
x_19 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_18, x_3, x_4, x_5, x_6, x_7, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_18, x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDecls_go___spec__1(x_14, x_1);
lean_ctor_set(x_11, 1, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_30 = l_Std_HashSetImp_insert___at_Lean_Compiler_LCNF_collectLocalDecls_go___spec__1(x_24, x_1);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_26);
x_32 = lean_st_ref_set(x_3, x_31, x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Compiler_LCNF_collectLocalDecls_go(x_14, x_1);
lean_ctor_set(x_11, 1, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_30 = l_Lean_Compiler_LCNF_collectLocalDecls_go(x_24, x_1);
x_31 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*6, x_26);
x_32 = lean_st_ref_set(x_3, x_31, x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_markUsedExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedExpr(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_Simp_markUsedExpr(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_AltCore_getCode(x_12);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_Simp_markUsedCode(x_13, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_1 = x_9;
x_7 = x_11;
goto _start;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_array_get_size(x_14);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_19, x_19);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_15);
x_25 = 0;
x_26 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_14, x_25, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_14);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_array_get_size(x_14);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_30, x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_14, x_38, x_39, x_40, x_2, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_14);
return x_41;
}
}
}
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
x_44 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_42, 3);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_array_get_size(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_49, x_49);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
lean_ctor_set(x_44, 0, x_54);
return x_44;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_44);
x_55 = 0;
x_56 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_57 = lean_box(0);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(x_48, x_55, x_56, x_57, x_2, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_48);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec(x_44);
x_60 = lean_ctor_get(x_42, 3);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_array_get_size(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_61, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(x_60, x_69, x_70, x_71, x_2, x_3, x_4, x_5, x_6, x_59);
lean_dec(x_60);
return x_72;
}
}
}
}
case 5:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_73, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
case 6:
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_7);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_79 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_77, x_2, x_3, x_4, x_5, x_6, x_7);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_1 = x_78;
x_7 = x_80;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedCode(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_13, x_1);
lean_dec(x_13);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_HashSetImp_contains___at_Lean_Compiler_LCNF_ElimDead_elimDead___spec__1(x_18, x_1);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_43; uint8_t x_44; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_43 = lean_array_get_size(x_1);
x_44 = lean_nat_dec_lt(x_14, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_46 = l_panic___at_Lean_Compiler_LCNF_attachCodeDecls_go___spec__1(x_45);
x_15 = x_46;
goto block_42;
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget(x_1, x_14);
x_15 = x_47;
goto block_42;
}
block_42:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_15);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
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
x_21 = l_Lean_Compiler_LCNF_eraseCodeDecl(x_15, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_2 = x_14;
x_9 = x_22;
goto _start;
}
else
{
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_25, x_4, x_5, x_6, x_7, x_8, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_14;
x_3 = x_28;
x_9 = x_27;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_31, x_4, x_5, x_6, x_7, x_8, x_30);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_14;
x_3 = x_34;
x_9 = x_33;
goto _start;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_37);
x_38 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_37, x_4, x_5, x_6, x_7, x_8, x_36);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_3);
x_2 = x_14;
x_3 = x_40;
x_9 = x_39;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_eraseCodeDecl(x_12, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1(x_1, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_eraseCodeDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5;
x_2 = l_Lean_instInhabitedFVarId;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.inlineProjInst?.visit", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
x_3 = lean_unsigned_to_nat(650u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
x_3 = lean_unsigned_to_nat(653u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = l_Lean_Compiler_LCNF_Simp_findExpr(x_1, x_10, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = 0;
lean_inc(x_12);
x_20 = l_Lean_Expr_constructorApp_x3f(x_18, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_21) == 4)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_22, x_7, x_8, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l_Lean_Compiler_LCNF_Decl_getArity(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_37);
x_39 = lean_nat_dec_eq(x_36, x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_24);
lean_inc(x_35);
x_41 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_35, x_23);
x_42 = lean_ctor_get(x_35, 3);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_38);
x_44 = lean_mk_array(x_38, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_38, x_45);
lean_dec(x_38);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_44, x_46);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_42, x_41, x_47, x_10, x_4, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_57 = lean_ctor_get(x_25, 0);
lean_inc(x_57);
lean_dec(x_25);
x_58 = l_Lean_Compiler_LCNF_Decl_getArity(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_59);
x_61 = lean_nat_dec_eq(x_58, x_60);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_57);
x_64 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_57, x_23);
x_65 = lean_ctor_get(x_57, 3);
lean_inc(x_65);
lean_dec(x_57);
x_66 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_60);
x_67 = lean_mk_array(x_60, x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_60, x_68);
lean_dec(x_60);
x_70 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_67, x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_71 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_65, x_64, x_70, x_10, x_4, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_65);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_24, 0);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_24);
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
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_17;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_16);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_12);
x_85 = lean_ctor_get(x_20, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_86 = x_20;
} else {
 lean_dec_ref(x_20);
 x_86 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_17);
x_87 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_88 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
lean_dec(x_2);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_nat_add(x_93, x_91);
lean_dec(x_91);
lean_dec(x_93);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_lt(x_94, x_95);
lean_dec(x_95);
x_97 = l_List_isEmpty___rarg(x_92);
if (x_96 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_90);
x_106 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_107 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_106);
x_98 = x_107;
goto block_105;
}
else
{
lean_object* x_108; 
x_108 = lean_array_fget(x_90, x_94);
lean_dec(x_94);
lean_dec(x_90);
x_98 = x_108;
goto block_105;
}
block_105:
{
if (x_97 == 0)
{
lean_dec(x_86);
lean_dec(x_17);
x_1 = x_98;
x_2 = x_92;
x_9 = x_16;
goto _start;
}
else
{
lean_dec(x_92);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
if (lean_is_scalar(x_86)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_86;
}
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_17)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_17;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_16);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_98);
lean_dec(x_86);
lean_dec(x_17);
x_103 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_104 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_104;
}
}
}
}
}
}
case 1:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_dec(x_11);
x_110 = lean_st_ref_get(x_8, x_109);
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
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = 0;
lean_inc(x_12);
x_116 = l_Lean_Expr_constructorApp_x3f(x_114, x_12, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_117) == 4)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_113);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_7);
x_120 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_118, x_7, x_8, x_112);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_119);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
x_124 = lean_box(0);
lean_ctor_set(x_120, 0, x_124);
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_120);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_120, 1);
x_130 = lean_ctor_get(x_120, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
lean_dec(x_121);
x_132 = l_Lean_Compiler_LCNF_Decl_getArity(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_133);
x_135 = lean_nat_dec_eq(x_132, x_134);
lean_dec(x_132);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_119);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_box(0);
lean_ctor_set(x_120, 0, x_136);
return x_120;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_120);
lean_inc(x_131);
x_137 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_131, x_119);
x_138 = lean_ctor_get(x_131, 3);
lean_inc(x_138);
lean_dec(x_131);
x_139 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_134);
x_140 = lean_mk_array(x_134, x_139);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_sub(x_134, x_141);
lean_dec(x_134);
x_143 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_140, x_142);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_144 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_138, x_137, x_143, x_10, x_4, x_5, x_6, x_7, x_8, x_129);
lean_dec(x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
return x_147;
}
else
{
uint8_t x_148; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_144);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_120, 1);
lean_inc(x_152);
lean_dec(x_120);
x_153 = lean_ctor_get(x_121, 0);
lean_inc(x_153);
lean_dec(x_121);
x_154 = l_Lean_Compiler_LCNF_Decl_getArity(x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_155);
x_157 = lean_nat_dec_eq(x_154, x_156);
lean_dec(x_154);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_119);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_inc(x_153);
x_160 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_153, x_119);
x_161 = lean_ctor_get(x_153, 3);
lean_inc(x_161);
lean_dec(x_153);
x_162 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_156);
x_163 = lean_mk_array(x_156, x_162);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_sub(x_156, x_164);
lean_dec(x_156);
x_166 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_163, x_165);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_167 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_161, x_160, x_166, x_10, x_4, x_5, x_6, x_7, x_8, x_152);
lean_dec(x_161);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_173 = x_167;
} else {
 lean_dec_ref(x_167);
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
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_119);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_120);
if (x_175 == 0)
{
return x_120;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_120, 0);
x_177 = lean_ctor_get(x_120, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_120);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_117);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_113;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_112);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_12);
x_181 = lean_ctor_get(x_116, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_182 = x_116;
} else {
 lean_dec_ref(x_116);
 x_182 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_113);
x_183 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_184 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_183, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_ctor_get(x_2, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 1);
lean_inc(x_188);
lean_dec(x_2);
x_189 = lean_ctor_get(x_185, 3);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_nat_add(x_189, x_187);
lean_dec(x_187);
lean_dec(x_189);
x_191 = lean_array_get_size(x_186);
x_192 = lean_nat_dec_lt(x_190, x_191);
lean_dec(x_191);
x_193 = l_List_isEmpty___rarg(x_188);
if (x_192 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_190);
lean_dec(x_186);
x_202 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_203 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_202);
x_194 = x_203;
goto block_201;
}
else
{
lean_object* x_204; 
x_204 = lean_array_fget(x_186, x_190);
lean_dec(x_190);
lean_dec(x_186);
x_194 = x_204;
goto block_201;
}
block_201:
{
if (x_193 == 0)
{
lean_dec(x_182);
lean_dec(x_113);
x_1 = x_194;
x_2 = x_188;
x_9 = x_112;
goto _start;
}
else
{
lean_dec(x_188);
if (lean_obj_tag(x_194) == 1)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
lean_dec(x_194);
if (lean_is_scalar(x_182)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_182;
}
lean_ctor_set(x_197, 0, x_196);
if (lean_is_scalar(x_113)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_113;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_112);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_194);
lean_dec(x_182);
lean_dec(x_113);
x_199 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_200 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_199, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
return x_200;
}
}
}
}
}
}
case 2:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_205 = lean_ctor_get(x_11, 1);
lean_inc(x_205);
lean_dec(x_11);
x_206 = lean_st_ref_get(x_8, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_207, 0);
lean_inc(x_210);
lean_dec(x_207);
x_211 = 0;
lean_inc(x_12);
x_212 = l_Lean_Expr_constructorApp_x3f(x_210, x_12, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_213) == 4)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_209);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_8);
lean_inc(x_7);
x_216 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_214, x_7, x_8, x_208);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
lean_dec(x_215);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_218 = !lean_is_exclusive(x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 0);
lean_dec(x_219);
x_220 = lean_box(0);
lean_ctor_set(x_216, 0, x_220);
return x_216;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_216, 1);
lean_inc(x_221);
lean_dec(x_216);
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_216);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_225 = lean_ctor_get(x_216, 1);
x_226 = lean_ctor_get(x_216, 0);
lean_dec(x_226);
x_227 = lean_ctor_get(x_217, 0);
lean_inc(x_227);
lean_dec(x_217);
x_228 = l_Lean_Compiler_LCNF_Decl_getArity(x_227);
x_229 = lean_unsigned_to_nat(0u);
x_230 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_229);
x_231 = lean_nat_dec_eq(x_228, x_230);
lean_dec(x_228);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_230);
lean_dec(x_227);
lean_dec(x_215);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_232 = lean_box(0);
lean_ctor_set(x_216, 0, x_232);
return x_216;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_216);
lean_inc(x_227);
x_233 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_227, x_215);
x_234 = lean_ctor_get(x_227, 3);
lean_inc(x_234);
lean_dec(x_227);
x_235 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_230);
x_236 = lean_mk_array(x_230, x_235);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_sub(x_230, x_237);
lean_dec(x_230);
x_239 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_236, x_238);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_240 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_234, x_233, x_239, x_10, x_4, x_5, x_6, x_7, x_8, x_225);
lean_dec(x_234);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_241, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_242);
return x_243;
}
else
{
uint8_t x_244; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
return x_240;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_240, 0);
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_240);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_216, 1);
lean_inc(x_248);
lean_dec(x_216);
x_249 = lean_ctor_get(x_217, 0);
lean_inc(x_249);
lean_dec(x_217);
x_250 = l_Lean_Compiler_LCNF_Decl_getArity(x_249);
x_251 = lean_unsigned_to_nat(0u);
x_252 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_251);
x_253 = lean_nat_dec_eq(x_250, x_252);
lean_dec(x_250);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_215);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_248);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_inc(x_249);
x_256 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_249, x_215);
x_257 = lean_ctor_get(x_249, 3);
lean_inc(x_257);
lean_dec(x_249);
x_258 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_252);
x_259 = lean_mk_array(x_252, x_258);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_sub(x_252, x_260);
lean_dec(x_252);
x_262 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_259, x_261);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_263 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_257, x_256, x_262, x_10, x_4, x_5, x_6, x_7, x_8, x_248);
lean_dec(x_257);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_264, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_265);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_269 = x_263;
} else {
 lean_dec_ref(x_263);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_215);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_271 = !lean_is_exclusive(x_216);
if (x_271 == 0)
{
return x_216;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_216, 0);
x_273 = lean_ctor_get(x_216, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_216);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_213);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_275 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_209;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_208);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_12);
x_277 = lean_ctor_get(x_212, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_278 = x_212;
} else {
 lean_dec_ref(x_212);
 x_278 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_209);
x_279 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_280 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_279, x_3, x_4, x_5, x_6, x_7, x_8, x_208);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
lean_dec(x_277);
x_283 = lean_ctor_get(x_2, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_2, 1);
lean_inc(x_284);
lean_dec(x_2);
x_285 = lean_ctor_get(x_281, 3);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_nat_add(x_285, x_283);
lean_dec(x_283);
lean_dec(x_285);
x_287 = lean_array_get_size(x_282);
x_288 = lean_nat_dec_lt(x_286, x_287);
lean_dec(x_287);
x_289 = l_List_isEmpty___rarg(x_284);
if (x_288 == 0)
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_286);
lean_dec(x_282);
x_298 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_299 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_298);
x_290 = x_299;
goto block_297;
}
else
{
lean_object* x_300; 
x_300 = lean_array_fget(x_282, x_286);
lean_dec(x_286);
lean_dec(x_282);
x_290 = x_300;
goto block_297;
}
block_297:
{
if (x_289 == 0)
{
lean_dec(x_278);
lean_dec(x_209);
x_1 = x_290;
x_2 = x_284;
x_9 = x_208;
goto _start;
}
else
{
lean_dec(x_284);
if (lean_obj_tag(x_290) == 1)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
lean_dec(x_290);
if (lean_is_scalar(x_278)) {
 x_293 = lean_alloc_ctor(1, 1, 0);
} else {
 x_293 = x_278;
}
lean_ctor_set(x_293, 0, x_292);
if (lean_is_scalar(x_209)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_209;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_208);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_290);
lean_dec(x_278);
lean_dec(x_209);
x_295 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_296 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_295, x_3, x_4, x_5, x_6, x_7, x_8, x_208);
return x_296;
}
}
}
}
}
}
case 3:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; 
x_301 = lean_ctor_get(x_11, 1);
lean_inc(x_301);
lean_dec(x_11);
x_302 = lean_st_ref_get(x_8, x_301);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_303, 0);
lean_inc(x_306);
lean_dec(x_303);
x_307 = 0;
lean_inc(x_12);
x_308 = l_Lean_Expr_constructorApp_x3f(x_306, x_12, x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
x_309 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_309) == 4)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_305);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_8);
lean_inc(x_7);
x_312 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_310, x_7, x_8, x_304);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
lean_dec(x_311);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_314 = !lean_is_exclusive(x_312);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_312, 0);
lean_dec(x_315);
x_316 = lean_box(0);
lean_ctor_set(x_312, 0, x_316);
return x_312;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
lean_dec(x_312);
x_318 = lean_box(0);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_312);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_321 = lean_ctor_get(x_312, 1);
x_322 = lean_ctor_get(x_312, 0);
lean_dec(x_322);
x_323 = lean_ctor_get(x_313, 0);
lean_inc(x_323);
lean_dec(x_313);
x_324 = l_Lean_Compiler_LCNF_Decl_getArity(x_323);
x_325 = lean_unsigned_to_nat(0u);
x_326 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_325);
x_327 = lean_nat_dec_eq(x_324, x_326);
lean_dec(x_324);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_326);
lean_dec(x_323);
lean_dec(x_311);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_328 = lean_box(0);
lean_ctor_set(x_312, 0, x_328);
return x_312;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_free_object(x_312);
lean_inc(x_323);
x_329 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_323, x_311);
x_330 = lean_ctor_get(x_323, 3);
lean_inc(x_330);
lean_dec(x_323);
x_331 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_326);
x_332 = lean_mk_array(x_326, x_331);
x_333 = lean_unsigned_to_nat(1u);
x_334 = lean_nat_sub(x_326, x_333);
lean_dec(x_326);
x_335 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_332, x_334);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_336 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_330, x_329, x_335, x_10, x_4, x_5, x_6, x_7, x_8, x_321);
lean_dec(x_330);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_338);
return x_339;
}
else
{
uint8_t x_340; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_340 = !lean_is_exclusive(x_336);
if (x_340 == 0)
{
return x_336;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_336, 0);
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_336);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_344 = lean_ctor_get(x_312, 1);
lean_inc(x_344);
lean_dec(x_312);
x_345 = lean_ctor_get(x_313, 0);
lean_inc(x_345);
lean_dec(x_313);
x_346 = l_Lean_Compiler_LCNF_Decl_getArity(x_345);
x_347 = lean_unsigned_to_nat(0u);
x_348 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_347);
x_349 = lean_nat_dec_eq(x_346, x_348);
lean_dec(x_346);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_311);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_350 = lean_box(0);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_344);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_inc(x_345);
x_352 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_345, x_311);
x_353 = lean_ctor_get(x_345, 3);
lean_inc(x_353);
lean_dec(x_345);
x_354 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_348);
x_355 = lean_mk_array(x_348, x_354);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_sub(x_348, x_356);
lean_dec(x_348);
x_358 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_355, x_357);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_359 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_353, x_352, x_358, x_10, x_4, x_5, x_6, x_7, x_8, x_344);
lean_dec(x_353);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_360, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_361);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_363 = lean_ctor_get(x_359, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_359, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_365 = x_359;
} else {
 lean_dec_ref(x_359);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
}
}
}
else
{
uint8_t x_367; 
lean_dec(x_311);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_367 = !lean_is_exclusive(x_312);
if (x_367 == 0)
{
return x_312;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_312, 0);
x_369 = lean_ctor_get(x_312, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_312);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_309);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_371 = lean_box(0);
if (lean_is_scalar(x_305)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_305;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_304);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_12);
x_373 = lean_ctor_get(x_308, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_374 = x_308;
} else {
 lean_dec_ref(x_308);
 x_374 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_305);
x_375 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_376 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_375, x_3, x_4, x_5, x_6, x_7, x_8, x_304);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; uint8_t x_385; lean_object* x_386; 
x_377 = lean_ctor_get(x_373, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_373, 1);
lean_inc(x_378);
lean_dec(x_373);
x_379 = lean_ctor_get(x_2, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_2, 1);
lean_inc(x_380);
lean_dec(x_2);
x_381 = lean_ctor_get(x_377, 3);
lean_inc(x_381);
lean_dec(x_377);
x_382 = lean_nat_add(x_381, x_379);
lean_dec(x_379);
lean_dec(x_381);
x_383 = lean_array_get_size(x_378);
x_384 = lean_nat_dec_lt(x_382, x_383);
lean_dec(x_383);
x_385 = l_List_isEmpty___rarg(x_380);
if (x_384 == 0)
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_382);
lean_dec(x_378);
x_394 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_395 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_394);
x_386 = x_395;
goto block_393;
}
else
{
lean_object* x_396; 
x_396 = lean_array_fget(x_378, x_382);
lean_dec(x_382);
lean_dec(x_378);
x_386 = x_396;
goto block_393;
}
block_393:
{
if (x_385 == 0)
{
lean_dec(x_374);
lean_dec(x_305);
x_1 = x_386;
x_2 = x_380;
x_9 = x_304;
goto _start;
}
else
{
lean_dec(x_380);
if (lean_obj_tag(x_386) == 1)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_388 = lean_ctor_get(x_386, 0);
lean_inc(x_388);
lean_dec(x_386);
if (lean_is_scalar(x_374)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_374;
}
lean_ctor_set(x_389, 0, x_388);
if (lean_is_scalar(x_305)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_305;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_304);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_386);
lean_dec(x_374);
lean_dec(x_305);
x_391 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_392 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_391, x_3, x_4, x_5, x_6, x_7, x_8, x_304);
return x_392;
}
}
}
}
}
}
case 4:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_397 = lean_ctor_get(x_11, 1);
lean_inc(x_397);
lean_dec(x_11);
x_398 = lean_st_ref_get(x_8, x_397);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_399, 0);
lean_inc(x_402);
lean_dec(x_399);
x_403 = 0;
lean_inc(x_12);
x_404 = l_Lean_Expr_constructorApp_x3f(x_402, x_12, x_403);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_405) == 4)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_401);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_8);
lean_inc(x_7);
x_408 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_406, x_7, x_8, x_400);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
uint8_t x_410; 
lean_dec(x_407);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_410 = !lean_is_exclusive(x_408);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_408, 0);
lean_dec(x_411);
x_412 = lean_box(0);
lean_ctor_set(x_408, 0, x_412);
return x_408;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_408, 1);
lean_inc(x_413);
lean_dec(x_408);
x_414 = lean_box(0);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
else
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_408);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_417 = lean_ctor_get(x_408, 1);
x_418 = lean_ctor_get(x_408, 0);
lean_dec(x_418);
x_419 = lean_ctor_get(x_409, 0);
lean_inc(x_419);
lean_dec(x_409);
x_420 = l_Lean_Compiler_LCNF_Decl_getArity(x_419);
x_421 = lean_unsigned_to_nat(0u);
x_422 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_421);
x_423 = lean_nat_dec_eq(x_420, x_422);
lean_dec(x_420);
if (x_423 == 0)
{
lean_object* x_424; 
lean_dec(x_422);
lean_dec(x_419);
lean_dec(x_407);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_424 = lean_box(0);
lean_ctor_set(x_408, 0, x_424);
return x_408;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_free_object(x_408);
lean_inc(x_419);
x_425 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_419, x_407);
x_426 = lean_ctor_get(x_419, 3);
lean_inc(x_426);
lean_dec(x_419);
x_427 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_422);
x_428 = lean_mk_array(x_422, x_427);
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_sub(x_422, x_429);
lean_dec(x_422);
x_431 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_428, x_430);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_432 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_426, x_425, x_431, x_10, x_4, x_5, x_6, x_7, x_8, x_417);
lean_dec(x_426);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_433, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_434);
return x_435;
}
else
{
uint8_t x_436; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_436 = !lean_is_exclusive(x_432);
if (x_436 == 0)
{
return x_432;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_432, 0);
x_438 = lean_ctor_get(x_432, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_432);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_440 = lean_ctor_get(x_408, 1);
lean_inc(x_440);
lean_dec(x_408);
x_441 = lean_ctor_get(x_409, 0);
lean_inc(x_441);
lean_dec(x_409);
x_442 = l_Lean_Compiler_LCNF_Decl_getArity(x_441);
x_443 = lean_unsigned_to_nat(0u);
x_444 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_443);
x_445 = lean_nat_dec_eq(x_442, x_444);
lean_dec(x_442);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_407);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_446 = lean_box(0);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_440);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_inc(x_441);
x_448 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_441, x_407);
x_449 = lean_ctor_get(x_441, 3);
lean_inc(x_449);
lean_dec(x_441);
x_450 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_444);
x_451 = lean_mk_array(x_444, x_450);
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_nat_sub(x_444, x_452);
lean_dec(x_444);
x_454 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_451, x_453);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_455 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_449, x_448, x_454, x_10, x_4, x_5, x_6, x_7, x_8, x_440);
lean_dec(x_449);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_456, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_455, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_461 = x_455;
} else {
 lean_dec_ref(x_455);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_407);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_463 = !lean_is_exclusive(x_408);
if (x_463 == 0)
{
return x_408;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_408, 0);
x_465 = lean_ctor_get(x_408, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_408);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_405);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_467 = lean_box(0);
if (lean_is_scalar(x_401)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_401;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_400);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_12);
x_469 = lean_ctor_get(x_404, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_470 = x_404;
} else {
 lean_dec_ref(x_404);
 x_470 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_401);
x_471 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_472 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_471, x_3, x_4, x_5, x_6, x_7, x_8, x_400);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; uint8_t x_481; lean_object* x_482; 
x_473 = lean_ctor_get(x_469, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_469, 1);
lean_inc(x_474);
lean_dec(x_469);
x_475 = lean_ctor_get(x_2, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_2, 1);
lean_inc(x_476);
lean_dec(x_2);
x_477 = lean_ctor_get(x_473, 3);
lean_inc(x_477);
lean_dec(x_473);
x_478 = lean_nat_add(x_477, x_475);
lean_dec(x_475);
lean_dec(x_477);
x_479 = lean_array_get_size(x_474);
x_480 = lean_nat_dec_lt(x_478, x_479);
lean_dec(x_479);
x_481 = l_List_isEmpty___rarg(x_476);
if (x_480 == 0)
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_478);
lean_dec(x_474);
x_490 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_491 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_490);
x_482 = x_491;
goto block_489;
}
else
{
lean_object* x_492; 
x_492 = lean_array_fget(x_474, x_478);
lean_dec(x_478);
lean_dec(x_474);
x_482 = x_492;
goto block_489;
}
block_489:
{
if (x_481 == 0)
{
lean_dec(x_470);
lean_dec(x_401);
x_1 = x_482;
x_2 = x_476;
x_9 = x_400;
goto _start;
}
else
{
lean_dec(x_476);
if (lean_obj_tag(x_482) == 1)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec(x_482);
if (lean_is_scalar(x_470)) {
 x_485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_485 = x_470;
}
lean_ctor_set(x_485, 0, x_484);
if (lean_is_scalar(x_401)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_401;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_400);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_482);
lean_dec(x_470);
lean_dec(x_401);
x_487 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_488 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_487, x_3, x_4, x_5, x_6, x_7, x_8, x_400);
return x_488;
}
}
}
}
}
}
case 5:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; lean_object* x_500; 
x_493 = lean_ctor_get(x_11, 1);
lean_inc(x_493);
lean_dec(x_11);
x_494 = lean_st_ref_get(x_8, x_493);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_497 = x_494;
} else {
 lean_dec_ref(x_494);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_495, 0);
lean_inc(x_498);
lean_dec(x_495);
x_499 = 0;
lean_inc(x_12);
x_500 = l_Lean_Expr_constructorApp_x3f(x_498, x_12, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; 
x_501 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_501) == 4)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_497);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
lean_inc(x_8);
lean_inc(x_7);
x_504 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_502, x_7, x_8, x_496);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
uint8_t x_506; 
lean_dec(x_503);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_506 = !lean_is_exclusive(x_504);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_504, 0);
lean_dec(x_507);
x_508 = lean_box(0);
lean_ctor_set(x_504, 0, x_508);
return x_504;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_504, 1);
lean_inc(x_509);
lean_dec(x_504);
x_510 = lean_box(0);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
else
{
uint8_t x_512; 
x_512 = !lean_is_exclusive(x_504);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_513 = lean_ctor_get(x_504, 1);
x_514 = lean_ctor_get(x_504, 0);
lean_dec(x_514);
x_515 = lean_ctor_get(x_505, 0);
lean_inc(x_515);
lean_dec(x_505);
x_516 = l_Lean_Compiler_LCNF_Decl_getArity(x_515);
x_517 = lean_unsigned_to_nat(0u);
x_518 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_517);
x_519 = lean_nat_dec_eq(x_516, x_518);
lean_dec(x_516);
if (x_519 == 0)
{
lean_object* x_520; 
lean_dec(x_518);
lean_dec(x_515);
lean_dec(x_503);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_520 = lean_box(0);
lean_ctor_set(x_504, 0, x_520);
return x_504;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_free_object(x_504);
lean_inc(x_515);
x_521 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_515, x_503);
x_522 = lean_ctor_get(x_515, 3);
lean_inc(x_522);
lean_dec(x_515);
x_523 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_518);
x_524 = lean_mk_array(x_518, x_523);
x_525 = lean_unsigned_to_nat(1u);
x_526 = lean_nat_sub(x_518, x_525);
lean_dec(x_518);
x_527 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_524, x_526);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_528 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_522, x_521, x_527, x_10, x_4, x_5, x_6, x_7, x_8, x_513);
lean_dec(x_522);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
x_531 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_529, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_530);
return x_531;
}
else
{
uint8_t x_532; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_532 = !lean_is_exclusive(x_528);
if (x_532 == 0)
{
return x_528;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_528, 0);
x_534 = lean_ctor_get(x_528, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_528);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
x_536 = lean_ctor_get(x_504, 1);
lean_inc(x_536);
lean_dec(x_504);
x_537 = lean_ctor_get(x_505, 0);
lean_inc(x_537);
lean_dec(x_505);
x_538 = l_Lean_Compiler_LCNF_Decl_getArity(x_537);
x_539 = lean_unsigned_to_nat(0u);
x_540 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_539);
x_541 = lean_nat_dec_eq(x_538, x_540);
lean_dec(x_538);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_540);
lean_dec(x_537);
lean_dec(x_503);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_542 = lean_box(0);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_536);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_inc(x_537);
x_544 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_537, x_503);
x_545 = lean_ctor_get(x_537, 3);
lean_inc(x_545);
lean_dec(x_537);
x_546 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_540);
x_547 = lean_mk_array(x_540, x_546);
x_548 = lean_unsigned_to_nat(1u);
x_549 = lean_nat_sub(x_540, x_548);
lean_dec(x_540);
x_550 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_547, x_549);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_551 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_545, x_544, x_550, x_10, x_4, x_5, x_6, x_7, x_8, x_536);
lean_dec(x_545);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_552, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_553);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_555 = lean_ctor_get(x_551, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_551, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_557 = x_551;
} else {
 lean_dec_ref(x_551);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
}
}
}
}
else
{
uint8_t x_559; 
lean_dec(x_503);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_559 = !lean_is_exclusive(x_504);
if (x_559 == 0)
{
return x_504;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_504, 0);
x_561 = lean_ctor_get(x_504, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_504);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_501);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_563 = lean_box(0);
if (lean_is_scalar(x_497)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_497;
}
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_496);
return x_564;
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_12);
x_565 = lean_ctor_get(x_500, 0);
lean_inc(x_565);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 x_566 = x_500;
} else {
 lean_dec_ref(x_500);
 x_566 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_497);
x_567 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_568 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_567, x_3, x_4, x_5, x_6, x_7, x_8, x_496);
return x_568;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; uint8_t x_577; lean_object* x_578; 
x_569 = lean_ctor_get(x_565, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_565, 1);
lean_inc(x_570);
lean_dec(x_565);
x_571 = lean_ctor_get(x_2, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_2, 1);
lean_inc(x_572);
lean_dec(x_2);
x_573 = lean_ctor_get(x_569, 3);
lean_inc(x_573);
lean_dec(x_569);
x_574 = lean_nat_add(x_573, x_571);
lean_dec(x_571);
lean_dec(x_573);
x_575 = lean_array_get_size(x_570);
x_576 = lean_nat_dec_lt(x_574, x_575);
lean_dec(x_575);
x_577 = l_List_isEmpty___rarg(x_572);
if (x_576 == 0)
{
lean_object* x_586; lean_object* x_587; 
lean_dec(x_574);
lean_dec(x_570);
x_586 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_587 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_586);
x_578 = x_587;
goto block_585;
}
else
{
lean_object* x_588; 
x_588 = lean_array_fget(x_570, x_574);
lean_dec(x_574);
lean_dec(x_570);
x_578 = x_588;
goto block_585;
}
block_585:
{
if (x_577 == 0)
{
lean_dec(x_566);
lean_dec(x_497);
x_1 = x_578;
x_2 = x_572;
x_9 = x_496;
goto _start;
}
else
{
lean_dec(x_572);
if (lean_obj_tag(x_578) == 1)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_580 = lean_ctor_get(x_578, 0);
lean_inc(x_580);
lean_dec(x_578);
if (lean_is_scalar(x_566)) {
 x_581 = lean_alloc_ctor(1, 1, 0);
} else {
 x_581 = x_566;
}
lean_ctor_set(x_581, 0, x_580);
if (lean_is_scalar(x_497)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_497;
}
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_496);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; 
lean_dec(x_578);
lean_dec(x_566);
lean_dec(x_497);
x_583 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_584 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_583, x_3, x_4, x_5, x_6, x_7, x_8, x_496);
return x_584;
}
}
}
}
}
}
case 6:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; 
x_589 = lean_ctor_get(x_11, 1);
lean_inc(x_589);
lean_dec(x_11);
x_590 = lean_st_ref_get(x_8, x_589);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_593 = x_590;
} else {
 lean_dec_ref(x_590);
 x_593 = lean_box(0);
}
x_594 = lean_ctor_get(x_591, 0);
lean_inc(x_594);
lean_dec(x_591);
x_595 = 0;
lean_inc(x_12);
x_596 = l_Lean_Expr_constructorApp_x3f(x_594, x_12, x_595);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; 
x_597 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_597) == 4)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_593);
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
lean_inc(x_8);
lean_inc(x_7);
x_600 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_598, x_7, x_8, x_592);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
if (lean_obj_tag(x_601) == 0)
{
uint8_t x_602; 
lean_dec(x_599);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_602 = !lean_is_exclusive(x_600);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_ctor_get(x_600, 0);
lean_dec(x_603);
x_604 = lean_box(0);
lean_ctor_set(x_600, 0, x_604);
return x_600;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_600, 1);
lean_inc(x_605);
lean_dec(x_600);
x_606 = lean_box(0);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
uint8_t x_608; 
x_608 = !lean_is_exclusive(x_600);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_609 = lean_ctor_get(x_600, 1);
x_610 = lean_ctor_get(x_600, 0);
lean_dec(x_610);
x_611 = lean_ctor_get(x_601, 0);
lean_inc(x_611);
lean_dec(x_601);
x_612 = l_Lean_Compiler_LCNF_Decl_getArity(x_611);
x_613 = lean_unsigned_to_nat(0u);
x_614 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_613);
x_615 = lean_nat_dec_eq(x_612, x_614);
lean_dec(x_612);
if (x_615 == 0)
{
lean_object* x_616; 
lean_dec(x_614);
lean_dec(x_611);
lean_dec(x_599);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_616 = lean_box(0);
lean_ctor_set(x_600, 0, x_616);
return x_600;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_free_object(x_600);
lean_inc(x_611);
x_617 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_611, x_599);
x_618 = lean_ctor_get(x_611, 3);
lean_inc(x_618);
lean_dec(x_611);
x_619 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_614);
x_620 = lean_mk_array(x_614, x_619);
x_621 = lean_unsigned_to_nat(1u);
x_622 = lean_nat_sub(x_614, x_621);
lean_dec(x_614);
x_623 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_620, x_622);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_624 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_618, x_617, x_623, x_10, x_4, x_5, x_6, x_7, x_8, x_609);
lean_dec(x_618);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_625, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_626);
return x_627;
}
else
{
uint8_t x_628; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_628 = !lean_is_exclusive(x_624);
if (x_628 == 0)
{
return x_624;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_624, 0);
x_630 = lean_ctor_get(x_624, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_624);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_632 = lean_ctor_get(x_600, 1);
lean_inc(x_632);
lean_dec(x_600);
x_633 = lean_ctor_get(x_601, 0);
lean_inc(x_633);
lean_dec(x_601);
x_634 = l_Lean_Compiler_LCNF_Decl_getArity(x_633);
x_635 = lean_unsigned_to_nat(0u);
x_636 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_635);
x_637 = lean_nat_dec_eq(x_634, x_636);
lean_dec(x_634);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_636);
lean_dec(x_633);
lean_dec(x_599);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_638 = lean_box(0);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_632);
return x_639;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_inc(x_633);
x_640 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_633, x_599);
x_641 = lean_ctor_get(x_633, 3);
lean_inc(x_641);
lean_dec(x_633);
x_642 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_636);
x_643 = lean_mk_array(x_636, x_642);
x_644 = lean_unsigned_to_nat(1u);
x_645 = lean_nat_sub(x_636, x_644);
lean_dec(x_636);
x_646 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_643, x_645);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_647 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_641, x_640, x_646, x_10, x_4, x_5, x_6, x_7, x_8, x_632);
lean_dec(x_641);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_648, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_649);
return x_650;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_651 = lean_ctor_get(x_647, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_647, 1);
lean_inc(x_652);
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 x_653 = x_647;
} else {
 lean_dec_ref(x_647);
 x_653 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_654 = lean_alloc_ctor(1, 2, 0);
} else {
 x_654 = x_653;
}
lean_ctor_set(x_654, 0, x_651);
lean_ctor_set(x_654, 1, x_652);
return x_654;
}
}
}
}
}
else
{
uint8_t x_655; 
lean_dec(x_599);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_655 = !lean_is_exclusive(x_600);
if (x_655 == 0)
{
return x_600;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_600, 0);
x_657 = lean_ctor_get(x_600, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_600);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
}
else
{
lean_object* x_659; lean_object* x_660; 
lean_dec(x_597);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_659 = lean_box(0);
if (lean_is_scalar(x_593)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_593;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_592);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_12);
x_661 = lean_ctor_get(x_596, 0);
lean_inc(x_661);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_662 = x_596;
} else {
 lean_dec_ref(x_596);
 x_662 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_593);
x_663 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_664 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_663, x_3, x_4, x_5, x_6, x_7, x_8, x_592);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; uint8_t x_673; lean_object* x_674; 
x_665 = lean_ctor_get(x_661, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_661, 1);
lean_inc(x_666);
lean_dec(x_661);
x_667 = lean_ctor_get(x_2, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_2, 1);
lean_inc(x_668);
lean_dec(x_2);
x_669 = lean_ctor_get(x_665, 3);
lean_inc(x_669);
lean_dec(x_665);
x_670 = lean_nat_add(x_669, x_667);
lean_dec(x_667);
lean_dec(x_669);
x_671 = lean_array_get_size(x_666);
x_672 = lean_nat_dec_lt(x_670, x_671);
lean_dec(x_671);
x_673 = l_List_isEmpty___rarg(x_668);
if (x_672 == 0)
{
lean_object* x_682; lean_object* x_683; 
lean_dec(x_670);
lean_dec(x_666);
x_682 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_683 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_682);
x_674 = x_683;
goto block_681;
}
else
{
lean_object* x_684; 
x_684 = lean_array_fget(x_666, x_670);
lean_dec(x_670);
lean_dec(x_666);
x_674 = x_684;
goto block_681;
}
block_681:
{
if (x_673 == 0)
{
lean_dec(x_662);
lean_dec(x_593);
x_1 = x_674;
x_2 = x_668;
x_9 = x_592;
goto _start;
}
else
{
lean_dec(x_668);
if (lean_obj_tag(x_674) == 1)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_676 = lean_ctor_get(x_674, 0);
lean_inc(x_676);
lean_dec(x_674);
if (lean_is_scalar(x_662)) {
 x_677 = lean_alloc_ctor(1, 1, 0);
} else {
 x_677 = x_662;
}
lean_ctor_set(x_677, 0, x_676);
if (lean_is_scalar(x_593)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_593;
}
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_592);
return x_678;
}
else
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_674);
lean_dec(x_662);
lean_dec(x_593);
x_679 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_680 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_679, x_3, x_4, x_5, x_6, x_7, x_8, x_592);
return x_680;
}
}
}
}
}
}
case 7:
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; lean_object* x_692; 
x_685 = lean_ctor_get(x_11, 1);
lean_inc(x_685);
lean_dec(x_11);
x_686 = lean_st_ref_get(x_8, x_685);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
x_690 = lean_ctor_get(x_687, 0);
lean_inc(x_690);
lean_dec(x_687);
x_691 = 0;
lean_inc(x_12);
x_692 = l_Lean_Expr_constructorApp_x3f(x_690, x_12, x_691);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; 
x_693 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_693) == 4)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_689);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
lean_inc(x_8);
lean_inc(x_7);
x_696 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_694, x_7, x_8, x_688);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
if (lean_obj_tag(x_697) == 0)
{
uint8_t x_698; 
lean_dec(x_695);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_698 = !lean_is_exclusive(x_696);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
x_699 = lean_ctor_get(x_696, 0);
lean_dec(x_699);
x_700 = lean_box(0);
lean_ctor_set(x_696, 0, x_700);
return x_696;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_696, 1);
lean_inc(x_701);
lean_dec(x_696);
x_702 = lean_box(0);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
uint8_t x_704; 
x_704 = !lean_is_exclusive(x_696);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; 
x_705 = lean_ctor_get(x_696, 1);
x_706 = lean_ctor_get(x_696, 0);
lean_dec(x_706);
x_707 = lean_ctor_get(x_697, 0);
lean_inc(x_707);
lean_dec(x_697);
x_708 = l_Lean_Compiler_LCNF_Decl_getArity(x_707);
x_709 = lean_unsigned_to_nat(0u);
x_710 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_709);
x_711 = lean_nat_dec_eq(x_708, x_710);
lean_dec(x_708);
if (x_711 == 0)
{
lean_object* x_712; 
lean_dec(x_710);
lean_dec(x_707);
lean_dec(x_695);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_712 = lean_box(0);
lean_ctor_set(x_696, 0, x_712);
return x_696;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_free_object(x_696);
lean_inc(x_707);
x_713 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_707, x_695);
x_714 = lean_ctor_get(x_707, 3);
lean_inc(x_714);
lean_dec(x_707);
x_715 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_710);
x_716 = lean_mk_array(x_710, x_715);
x_717 = lean_unsigned_to_nat(1u);
x_718 = lean_nat_sub(x_710, x_717);
lean_dec(x_710);
x_719 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_716, x_718);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_720 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_714, x_713, x_719, x_10, x_4, x_5, x_6, x_7, x_8, x_705);
lean_dec(x_714);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
x_723 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_721, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_722);
return x_723;
}
else
{
uint8_t x_724; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_724 = !lean_is_exclusive(x_720);
if (x_724 == 0)
{
return x_720;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_720, 0);
x_726 = lean_ctor_get(x_720, 1);
lean_inc(x_726);
lean_inc(x_725);
lean_dec(x_720);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set(x_727, 1, x_726);
return x_727;
}
}
}
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; uint8_t x_733; 
x_728 = lean_ctor_get(x_696, 1);
lean_inc(x_728);
lean_dec(x_696);
x_729 = lean_ctor_get(x_697, 0);
lean_inc(x_729);
lean_dec(x_697);
x_730 = l_Lean_Compiler_LCNF_Decl_getArity(x_729);
x_731 = lean_unsigned_to_nat(0u);
x_732 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_731);
x_733 = lean_nat_dec_eq(x_730, x_732);
lean_dec(x_730);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; 
lean_dec(x_732);
lean_dec(x_729);
lean_dec(x_695);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_734 = lean_box(0);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_728);
return x_735;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_inc(x_729);
x_736 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_729, x_695);
x_737 = lean_ctor_get(x_729, 3);
lean_inc(x_737);
lean_dec(x_729);
x_738 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_732);
x_739 = lean_mk_array(x_732, x_738);
x_740 = lean_unsigned_to_nat(1u);
x_741 = lean_nat_sub(x_732, x_740);
lean_dec(x_732);
x_742 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_739, x_741);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_743 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_737, x_736, x_742, x_10, x_4, x_5, x_6, x_7, x_8, x_728);
lean_dec(x_737);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_744, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_745);
return x_746;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_747 = lean_ctor_get(x_743, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_743, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_749 = x_743;
} else {
 lean_dec_ref(x_743);
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
}
}
}
else
{
uint8_t x_751; 
lean_dec(x_695);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_751 = !lean_is_exclusive(x_696);
if (x_751 == 0)
{
return x_696;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_696, 0);
x_753 = lean_ctor_get(x_696, 1);
lean_inc(x_753);
lean_inc(x_752);
lean_dec(x_696);
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
return x_754;
}
}
}
else
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_693);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_755 = lean_box(0);
if (lean_is_scalar(x_689)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_689;
}
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_688);
return x_756;
}
}
else
{
lean_object* x_757; lean_object* x_758; 
lean_dec(x_12);
x_757 = lean_ctor_get(x_692, 0);
lean_inc(x_757);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 x_758 = x_692;
} else {
 lean_dec_ref(x_692);
 x_758 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_759; lean_object* x_760; 
lean_dec(x_758);
lean_dec(x_757);
lean_dec(x_689);
x_759 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_760 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_759, x_3, x_4, x_5, x_6, x_7, x_8, x_688);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_768; uint8_t x_769; lean_object* x_770; 
x_761 = lean_ctor_get(x_757, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_757, 1);
lean_inc(x_762);
lean_dec(x_757);
x_763 = lean_ctor_get(x_2, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_2, 1);
lean_inc(x_764);
lean_dec(x_2);
x_765 = lean_ctor_get(x_761, 3);
lean_inc(x_765);
lean_dec(x_761);
x_766 = lean_nat_add(x_765, x_763);
lean_dec(x_763);
lean_dec(x_765);
x_767 = lean_array_get_size(x_762);
x_768 = lean_nat_dec_lt(x_766, x_767);
lean_dec(x_767);
x_769 = l_List_isEmpty___rarg(x_764);
if (x_768 == 0)
{
lean_object* x_778; lean_object* x_779; 
lean_dec(x_766);
lean_dec(x_762);
x_778 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_779 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_778);
x_770 = x_779;
goto block_777;
}
else
{
lean_object* x_780; 
x_780 = lean_array_fget(x_762, x_766);
lean_dec(x_766);
lean_dec(x_762);
x_770 = x_780;
goto block_777;
}
block_777:
{
if (x_769 == 0)
{
lean_dec(x_758);
lean_dec(x_689);
x_1 = x_770;
x_2 = x_764;
x_9 = x_688;
goto _start;
}
else
{
lean_dec(x_764);
if (lean_obj_tag(x_770) == 1)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_772 = lean_ctor_get(x_770, 0);
lean_inc(x_772);
lean_dec(x_770);
if (lean_is_scalar(x_758)) {
 x_773 = lean_alloc_ctor(1, 1, 0);
} else {
 x_773 = x_758;
}
lean_ctor_set(x_773, 0, x_772);
if (lean_is_scalar(x_689)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_689;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_688);
return x_774;
}
else
{
lean_object* x_775; lean_object* x_776; 
lean_dec(x_770);
lean_dec(x_758);
lean_dec(x_689);
x_775 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_776 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_775, x_3, x_4, x_5, x_6, x_7, x_8, x_688);
return x_776;
}
}
}
}
}
}
case 8:
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; lean_object* x_788; 
x_781 = lean_ctor_get(x_11, 1);
lean_inc(x_781);
lean_dec(x_11);
x_782 = lean_st_ref_get(x_8, x_781);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_785 = x_782;
} else {
 lean_dec_ref(x_782);
 x_785 = lean_box(0);
}
x_786 = lean_ctor_get(x_783, 0);
lean_inc(x_786);
lean_dec(x_783);
x_787 = 0;
lean_inc(x_12);
x_788 = l_Lean_Expr_constructorApp_x3f(x_786, x_12, x_787);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; 
x_789 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_789) == 4)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec(x_785);
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
lean_inc(x_8);
lean_inc(x_7);
x_792 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_790, x_7, x_8, x_784);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
if (lean_obj_tag(x_793) == 0)
{
uint8_t x_794; 
lean_dec(x_791);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_794 = !lean_is_exclusive(x_792);
if (x_794 == 0)
{
lean_object* x_795; lean_object* x_796; 
x_795 = lean_ctor_get(x_792, 0);
lean_dec(x_795);
x_796 = lean_box(0);
lean_ctor_set(x_792, 0, x_796);
return x_792;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_792, 1);
lean_inc(x_797);
lean_dec(x_792);
x_798 = lean_box(0);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_798);
lean_ctor_set(x_799, 1, x_797);
return x_799;
}
}
else
{
uint8_t x_800; 
x_800 = !lean_is_exclusive(x_792);
if (x_800 == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; 
x_801 = lean_ctor_get(x_792, 1);
x_802 = lean_ctor_get(x_792, 0);
lean_dec(x_802);
x_803 = lean_ctor_get(x_793, 0);
lean_inc(x_803);
lean_dec(x_793);
x_804 = l_Lean_Compiler_LCNF_Decl_getArity(x_803);
x_805 = lean_unsigned_to_nat(0u);
x_806 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_805);
x_807 = lean_nat_dec_eq(x_804, x_806);
lean_dec(x_804);
if (x_807 == 0)
{
lean_object* x_808; 
lean_dec(x_806);
lean_dec(x_803);
lean_dec(x_791);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_808 = lean_box(0);
lean_ctor_set(x_792, 0, x_808);
return x_792;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_free_object(x_792);
lean_inc(x_803);
x_809 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_803, x_791);
x_810 = lean_ctor_get(x_803, 3);
lean_inc(x_810);
lean_dec(x_803);
x_811 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_806);
x_812 = lean_mk_array(x_806, x_811);
x_813 = lean_unsigned_to_nat(1u);
x_814 = lean_nat_sub(x_806, x_813);
lean_dec(x_806);
x_815 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_812, x_814);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_816 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_810, x_809, x_815, x_10, x_4, x_5, x_6, x_7, x_8, x_801);
lean_dec(x_810);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_817, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_818);
return x_819;
}
else
{
uint8_t x_820; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_820 = !lean_is_exclusive(x_816);
if (x_820 == 0)
{
return x_816;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_816, 0);
x_822 = lean_ctor_get(x_816, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_816);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; 
x_824 = lean_ctor_get(x_792, 1);
lean_inc(x_824);
lean_dec(x_792);
x_825 = lean_ctor_get(x_793, 0);
lean_inc(x_825);
lean_dec(x_793);
x_826 = l_Lean_Compiler_LCNF_Decl_getArity(x_825);
x_827 = lean_unsigned_to_nat(0u);
x_828 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_827);
x_829 = lean_nat_dec_eq(x_826, x_828);
lean_dec(x_826);
if (x_829 == 0)
{
lean_object* x_830; lean_object* x_831; 
lean_dec(x_828);
lean_dec(x_825);
lean_dec(x_791);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_830 = lean_box(0);
x_831 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_824);
return x_831;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_inc(x_825);
x_832 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_825, x_791);
x_833 = lean_ctor_get(x_825, 3);
lean_inc(x_833);
lean_dec(x_825);
x_834 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_828);
x_835 = lean_mk_array(x_828, x_834);
x_836 = lean_unsigned_to_nat(1u);
x_837 = lean_nat_sub(x_828, x_836);
lean_dec(x_828);
x_838 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_835, x_837);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_839 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_833, x_832, x_838, x_10, x_4, x_5, x_6, x_7, x_8, x_824);
lean_dec(x_833);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_840, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_841);
return x_842;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_843 = lean_ctor_get(x_839, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_839, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_845 = x_839;
} else {
 lean_dec_ref(x_839);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
}
}
}
else
{
uint8_t x_847; 
lean_dec(x_791);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_847 = !lean_is_exclusive(x_792);
if (x_847 == 0)
{
return x_792;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_848 = lean_ctor_get(x_792, 0);
x_849 = lean_ctor_get(x_792, 1);
lean_inc(x_849);
lean_inc(x_848);
lean_dec(x_792);
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_849);
return x_850;
}
}
}
else
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_789);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_851 = lean_box(0);
if (lean_is_scalar(x_785)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_785;
}
lean_ctor_set(x_852, 0, x_851);
lean_ctor_set(x_852, 1, x_784);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; 
lean_dec(x_12);
x_853 = lean_ctor_get(x_788, 0);
lean_inc(x_853);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 x_854 = x_788;
} else {
 lean_dec_ref(x_788);
 x_854 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_855; lean_object* x_856; 
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_785);
x_855 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_856 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_855, x_3, x_4, x_5, x_6, x_7, x_8, x_784);
return x_856;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; uint8_t x_865; lean_object* x_866; 
x_857 = lean_ctor_get(x_853, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_853, 1);
lean_inc(x_858);
lean_dec(x_853);
x_859 = lean_ctor_get(x_2, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_2, 1);
lean_inc(x_860);
lean_dec(x_2);
x_861 = lean_ctor_get(x_857, 3);
lean_inc(x_861);
lean_dec(x_857);
x_862 = lean_nat_add(x_861, x_859);
lean_dec(x_859);
lean_dec(x_861);
x_863 = lean_array_get_size(x_858);
x_864 = lean_nat_dec_lt(x_862, x_863);
lean_dec(x_863);
x_865 = l_List_isEmpty___rarg(x_860);
if (x_864 == 0)
{
lean_object* x_874; lean_object* x_875; 
lean_dec(x_862);
lean_dec(x_858);
x_874 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_875 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_874);
x_866 = x_875;
goto block_873;
}
else
{
lean_object* x_876; 
x_876 = lean_array_fget(x_858, x_862);
lean_dec(x_862);
lean_dec(x_858);
x_866 = x_876;
goto block_873;
}
block_873:
{
if (x_865 == 0)
{
lean_dec(x_854);
lean_dec(x_785);
x_1 = x_866;
x_2 = x_860;
x_9 = x_784;
goto _start;
}
else
{
lean_dec(x_860);
if (lean_obj_tag(x_866) == 1)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_868 = lean_ctor_get(x_866, 0);
lean_inc(x_868);
lean_dec(x_866);
if (lean_is_scalar(x_854)) {
 x_869 = lean_alloc_ctor(1, 1, 0);
} else {
 x_869 = x_854;
}
lean_ctor_set(x_869, 0, x_868);
if (lean_is_scalar(x_785)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_785;
}
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_784);
return x_870;
}
else
{
lean_object* x_871; lean_object* x_872; 
lean_dec(x_866);
lean_dec(x_854);
lean_dec(x_785);
x_871 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_872 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_871, x_3, x_4, x_5, x_6, x_7, x_8, x_784);
return x_872;
}
}
}
}
}
}
case 9:
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; lean_object* x_884; 
x_877 = lean_ctor_get(x_11, 1);
lean_inc(x_877);
lean_dec(x_11);
x_878 = lean_st_ref_get(x_8, x_877);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_881 = x_878;
} else {
 lean_dec_ref(x_878);
 x_881 = lean_box(0);
}
x_882 = lean_ctor_get(x_879, 0);
lean_inc(x_882);
lean_dec(x_879);
x_883 = 0;
lean_inc(x_12);
x_884 = l_Lean_Expr_constructorApp_x3f(x_882, x_12, x_883);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; 
x_885 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_885) == 4)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_881);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
lean_inc(x_8);
lean_inc(x_7);
x_888 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_886, x_7, x_8, x_880);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
if (lean_obj_tag(x_889) == 0)
{
uint8_t x_890; 
lean_dec(x_887);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_890 = !lean_is_exclusive(x_888);
if (x_890 == 0)
{
lean_object* x_891; lean_object* x_892; 
x_891 = lean_ctor_get(x_888, 0);
lean_dec(x_891);
x_892 = lean_box(0);
lean_ctor_set(x_888, 0, x_892);
return x_888;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_888, 1);
lean_inc(x_893);
lean_dec(x_888);
x_894 = lean_box(0);
x_895 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_893);
return x_895;
}
}
else
{
uint8_t x_896; 
x_896 = !lean_is_exclusive(x_888);
if (x_896 == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; uint8_t x_903; 
x_897 = lean_ctor_get(x_888, 1);
x_898 = lean_ctor_get(x_888, 0);
lean_dec(x_898);
x_899 = lean_ctor_get(x_889, 0);
lean_inc(x_899);
lean_dec(x_889);
x_900 = l_Lean_Compiler_LCNF_Decl_getArity(x_899);
x_901 = lean_unsigned_to_nat(0u);
x_902 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_901);
x_903 = lean_nat_dec_eq(x_900, x_902);
lean_dec(x_900);
if (x_903 == 0)
{
lean_object* x_904; 
lean_dec(x_902);
lean_dec(x_899);
lean_dec(x_887);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_904 = lean_box(0);
lean_ctor_set(x_888, 0, x_904);
return x_888;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_free_object(x_888);
lean_inc(x_899);
x_905 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_899, x_887);
x_906 = lean_ctor_get(x_899, 3);
lean_inc(x_906);
lean_dec(x_899);
x_907 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_902);
x_908 = lean_mk_array(x_902, x_907);
x_909 = lean_unsigned_to_nat(1u);
x_910 = lean_nat_sub(x_902, x_909);
lean_dec(x_902);
x_911 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_908, x_910);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_912 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_906, x_905, x_911, x_10, x_4, x_5, x_6, x_7, x_8, x_897);
lean_dec(x_906);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_913, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_914);
return x_915;
}
else
{
uint8_t x_916; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_916 = !lean_is_exclusive(x_912);
if (x_916 == 0)
{
return x_912;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_912, 0);
x_918 = lean_ctor_get(x_912, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_912);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
}
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_920 = lean_ctor_get(x_888, 1);
lean_inc(x_920);
lean_dec(x_888);
x_921 = lean_ctor_get(x_889, 0);
lean_inc(x_921);
lean_dec(x_889);
x_922 = l_Lean_Compiler_LCNF_Decl_getArity(x_921);
x_923 = lean_unsigned_to_nat(0u);
x_924 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_923);
x_925 = lean_nat_dec_eq(x_922, x_924);
lean_dec(x_922);
if (x_925 == 0)
{
lean_object* x_926; lean_object* x_927; 
lean_dec(x_924);
lean_dec(x_921);
lean_dec(x_887);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_926 = lean_box(0);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_926);
lean_ctor_set(x_927, 1, x_920);
return x_927;
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_inc(x_921);
x_928 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_921, x_887);
x_929 = lean_ctor_get(x_921, 3);
lean_inc(x_929);
lean_dec(x_921);
x_930 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_924);
x_931 = lean_mk_array(x_924, x_930);
x_932 = lean_unsigned_to_nat(1u);
x_933 = lean_nat_sub(x_924, x_932);
lean_dec(x_924);
x_934 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_931, x_933);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_935 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_929, x_928, x_934, x_10, x_4, x_5, x_6, x_7, x_8, x_920);
lean_dec(x_929);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_936, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_937);
return x_938;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_939 = lean_ctor_get(x_935, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_935, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_941 = x_935;
} else {
 lean_dec_ref(x_935);
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
}
}
}
else
{
uint8_t x_943; 
lean_dec(x_887);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_943 = !lean_is_exclusive(x_888);
if (x_943 == 0)
{
return x_888;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_888, 0);
x_945 = lean_ctor_get(x_888, 1);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_888);
x_946 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_946, 0, x_944);
lean_ctor_set(x_946, 1, x_945);
return x_946;
}
}
}
else
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_885);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_947 = lean_box(0);
if (lean_is_scalar(x_881)) {
 x_948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_948 = x_881;
}
lean_ctor_set(x_948, 0, x_947);
lean_ctor_set(x_948, 1, x_880);
return x_948;
}
}
else
{
lean_object* x_949; lean_object* x_950; 
lean_dec(x_12);
x_949 = lean_ctor_get(x_884, 0);
lean_inc(x_949);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 x_950 = x_884;
} else {
 lean_dec_ref(x_884);
 x_950 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_951; lean_object* x_952; 
lean_dec(x_950);
lean_dec(x_949);
lean_dec(x_881);
x_951 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_952 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_951, x_3, x_4, x_5, x_6, x_7, x_8, x_880);
return x_952;
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; uint8_t x_961; lean_object* x_962; 
x_953 = lean_ctor_get(x_949, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_949, 1);
lean_inc(x_954);
lean_dec(x_949);
x_955 = lean_ctor_get(x_2, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_2, 1);
lean_inc(x_956);
lean_dec(x_2);
x_957 = lean_ctor_get(x_953, 3);
lean_inc(x_957);
lean_dec(x_953);
x_958 = lean_nat_add(x_957, x_955);
lean_dec(x_955);
lean_dec(x_957);
x_959 = lean_array_get_size(x_954);
x_960 = lean_nat_dec_lt(x_958, x_959);
lean_dec(x_959);
x_961 = l_List_isEmpty___rarg(x_956);
if (x_960 == 0)
{
lean_object* x_970; lean_object* x_971; 
lean_dec(x_958);
lean_dec(x_954);
x_970 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_971 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_970);
x_962 = x_971;
goto block_969;
}
else
{
lean_object* x_972; 
x_972 = lean_array_fget(x_954, x_958);
lean_dec(x_958);
lean_dec(x_954);
x_962 = x_972;
goto block_969;
}
block_969:
{
if (x_961 == 0)
{
lean_dec(x_950);
lean_dec(x_881);
x_1 = x_962;
x_2 = x_956;
x_9 = x_880;
goto _start;
}
else
{
lean_dec(x_956);
if (lean_obj_tag(x_962) == 1)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_964 = lean_ctor_get(x_962, 0);
lean_inc(x_964);
lean_dec(x_962);
if (lean_is_scalar(x_950)) {
 x_965 = lean_alloc_ctor(1, 1, 0);
} else {
 x_965 = x_950;
}
lean_ctor_set(x_965, 0, x_964);
if (lean_is_scalar(x_881)) {
 x_966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_966 = x_881;
}
lean_ctor_set(x_966, 0, x_965);
lean_ctor_set(x_966, 1, x_880);
return x_966;
}
else
{
lean_object* x_967; lean_object* x_968; 
lean_dec(x_962);
lean_dec(x_950);
lean_dec(x_881);
x_967 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_968 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_967, x_3, x_4, x_5, x_6, x_7, x_8, x_880);
return x_968;
}
}
}
}
}
}
case 10:
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; lean_object* x_980; 
x_973 = lean_ctor_get(x_11, 1);
lean_inc(x_973);
lean_dec(x_11);
x_974 = lean_st_ref_get(x_8, x_973);
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_977 = x_974;
} else {
 lean_dec_ref(x_974);
 x_977 = lean_box(0);
}
x_978 = lean_ctor_get(x_975, 0);
lean_inc(x_978);
lean_dec(x_975);
x_979 = 0;
lean_inc(x_12);
x_980 = l_Lean_Expr_constructorApp_x3f(x_978, x_12, x_979);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; 
x_981 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_981) == 4)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_977);
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec(x_981);
lean_inc(x_8);
lean_inc(x_7);
x_984 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_982, x_7, x_8, x_976);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
if (lean_obj_tag(x_985) == 0)
{
uint8_t x_986; 
lean_dec(x_983);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_986 = !lean_is_exclusive(x_984);
if (x_986 == 0)
{
lean_object* x_987; lean_object* x_988; 
x_987 = lean_ctor_get(x_984, 0);
lean_dec(x_987);
x_988 = lean_box(0);
lean_ctor_set(x_984, 0, x_988);
return x_984;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_984, 1);
lean_inc(x_989);
lean_dec(x_984);
x_990 = lean_box(0);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_990);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
else
{
uint8_t x_992; 
x_992 = !lean_is_exclusive(x_984);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; 
x_993 = lean_ctor_get(x_984, 1);
x_994 = lean_ctor_get(x_984, 0);
lean_dec(x_994);
x_995 = lean_ctor_get(x_985, 0);
lean_inc(x_995);
lean_dec(x_985);
x_996 = l_Lean_Compiler_LCNF_Decl_getArity(x_995);
x_997 = lean_unsigned_to_nat(0u);
x_998 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_997);
x_999 = lean_nat_dec_eq(x_996, x_998);
lean_dec(x_996);
if (x_999 == 0)
{
lean_object* x_1000; 
lean_dec(x_998);
lean_dec(x_995);
lean_dec(x_983);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1000 = lean_box(0);
lean_ctor_set(x_984, 0, x_1000);
return x_984;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
lean_free_object(x_984);
lean_inc(x_995);
x_1001 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_995, x_983);
x_1002 = lean_ctor_get(x_995, 3);
lean_inc(x_1002);
lean_dec(x_995);
x_1003 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_998);
x_1004 = lean_mk_array(x_998, x_1003);
x_1005 = lean_unsigned_to_nat(1u);
x_1006 = lean_nat_sub(x_998, x_1005);
lean_dec(x_998);
x_1007 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_1004, x_1006);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1008 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1002, x_1001, x_1007, x_10, x_4, x_5, x_6, x_7, x_8, x_993);
lean_dec(x_1002);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec(x_1008);
x_1011 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_1009, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1010);
return x_1011;
}
else
{
uint8_t x_1012; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1012 = !lean_is_exclusive(x_1008);
if (x_1012 == 0)
{
return x_1008;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_1008, 0);
x_1014 = lean_ctor_get(x_1008, 1);
lean_inc(x_1014);
lean_inc(x_1013);
lean_dec(x_1008);
x_1015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1015, 0, x_1013);
lean_ctor_set(x_1015, 1, x_1014);
return x_1015;
}
}
}
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
x_1016 = lean_ctor_get(x_984, 1);
lean_inc(x_1016);
lean_dec(x_984);
x_1017 = lean_ctor_get(x_985, 0);
lean_inc(x_1017);
lean_dec(x_985);
x_1018 = l_Lean_Compiler_LCNF_Decl_getArity(x_1017);
x_1019 = lean_unsigned_to_nat(0u);
x_1020 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_1019);
x_1021 = lean_nat_dec_eq(x_1018, x_1020);
lean_dec(x_1018);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_1020);
lean_dec(x_1017);
lean_dec(x_983);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1022 = lean_box(0);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1016);
return x_1023;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_inc(x_1017);
x_1024 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_1017, x_983);
x_1025 = lean_ctor_get(x_1017, 3);
lean_inc(x_1025);
lean_dec(x_1017);
x_1026 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_1020);
x_1027 = lean_mk_array(x_1020, x_1026);
x_1028 = lean_unsigned_to_nat(1u);
x_1029 = lean_nat_sub(x_1020, x_1028);
lean_dec(x_1020);
x_1030 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_1027, x_1029);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1031 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1025, x_1024, x_1030, x_10, x_4, x_5, x_6, x_7, x_8, x_1016);
lean_dec(x_1025);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_1032, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1033);
return x_1034;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1035 = lean_ctor_get(x_1031, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1031, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1037 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1037 = lean_box(0);
}
if (lean_is_scalar(x_1037)) {
 x_1038 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1038 = x_1037;
}
lean_ctor_set(x_1038, 0, x_1035);
lean_ctor_set(x_1038, 1, x_1036);
return x_1038;
}
}
}
}
}
else
{
uint8_t x_1039; 
lean_dec(x_983);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1039 = !lean_is_exclusive(x_984);
if (x_1039 == 0)
{
return x_984;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_984, 0);
x_1041 = lean_ctor_get(x_984, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_984);
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
}
else
{
lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_981);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1043 = lean_box(0);
if (lean_is_scalar(x_977)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_977;
}
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_976);
return x_1044;
}
}
else
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_12);
x_1045 = lean_ctor_get(x_980, 0);
lean_inc(x_1045);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 x_1046 = x_980;
} else {
 lean_dec_ref(x_980);
 x_1046 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1046);
lean_dec(x_1045);
lean_dec(x_977);
x_1047 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_1048 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_1047, x_3, x_4, x_5, x_6, x_7, x_8, x_976);
return x_1048;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; uint8_t x_1056; uint8_t x_1057; lean_object* x_1058; 
x_1049 = lean_ctor_get(x_1045, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1045, 1);
lean_inc(x_1050);
lean_dec(x_1045);
x_1051 = lean_ctor_get(x_2, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_2, 1);
lean_inc(x_1052);
lean_dec(x_2);
x_1053 = lean_ctor_get(x_1049, 3);
lean_inc(x_1053);
lean_dec(x_1049);
x_1054 = lean_nat_add(x_1053, x_1051);
lean_dec(x_1051);
lean_dec(x_1053);
x_1055 = lean_array_get_size(x_1050);
x_1056 = lean_nat_dec_lt(x_1054, x_1055);
lean_dec(x_1055);
x_1057 = l_List_isEmpty___rarg(x_1052);
if (x_1056 == 0)
{
lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_1054);
lean_dec(x_1050);
x_1066 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_1067 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_1066);
x_1058 = x_1067;
goto block_1065;
}
else
{
lean_object* x_1068; 
x_1068 = lean_array_fget(x_1050, x_1054);
lean_dec(x_1054);
lean_dec(x_1050);
x_1058 = x_1068;
goto block_1065;
}
block_1065:
{
if (x_1057 == 0)
{
lean_dec(x_1046);
lean_dec(x_977);
x_1 = x_1058;
x_2 = x_1052;
x_9 = x_976;
goto _start;
}
else
{
lean_dec(x_1052);
if (lean_obj_tag(x_1058) == 1)
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1060 = lean_ctor_get(x_1058, 0);
lean_inc(x_1060);
lean_dec(x_1058);
if (lean_is_scalar(x_1046)) {
 x_1061 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1061 = x_1046;
}
lean_ctor_set(x_1061, 0, x_1060);
if (lean_is_scalar(x_977)) {
 x_1062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1062 = x_977;
}
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_976);
return x_1062;
}
else
{
lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_1058);
lean_dec(x_1046);
lean_dec(x_977);
x_1063 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_1064 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_1063, x_3, x_4, x_5, x_6, x_7, x_8, x_976);
return x_1064;
}
}
}
}
}
}
default: 
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1069 = lean_ctor_get(x_11, 1);
lean_inc(x_1069);
lean_dec(x_11);
x_1070 = lean_ctor_get(x_12, 1);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_12, 2);
lean_inc(x_1071);
lean_dec(x_12);
x_1072 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1072, 0, x_1070);
lean_ctor_set(x_1072, 1, x_2);
x_1 = x_1071;
x_2 = x_1072;
x_9 = x_1069;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = lean_array_push(x_15, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_16);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_11;
x_9 = x_20;
goto _start;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_st_ref_get(x_8, x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_22);
x_30 = lean_array_push(x_27, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_1 = x_23;
x_9 = x_32;
goto _start;
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_Expr_fvar___override(x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(x_2, x_11, x_16, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_Simp_eraseCodeDecls(x_24, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
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
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_19, 0, x_37);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_23, 0, x_41);
return x_23;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_45 = x_19;
} else {
 lean_dec_ref(x_19);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_Compiler_LCNF_inferType(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_isClass_x3f(x_12, x_8, x_9, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_inferType(x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_isClass_x3f(x_11, x_5, x_6, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(x_1, x_8, x_9, x_22, x_2, x_3, x_4, x_5, x_6, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget(x_9, x_15);
lean_dec(x_9);
x_17 = lean_st_ref_get(x_6, x_7);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_22, x_16);
x_24 = 1;
x_25 = l_Lean_Compiler_LCNF_Simp_findExpr(x_23, x_24, x_4, x_5, x_6, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_isConstructorApp(x_32, x_26);
lean_dec(x_26);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_8);
x_34 = lean_box(0);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_28);
x_35 = lean_st_ref_get(x_6, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_3, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_40, x_8);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_45, x_8);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_isConstructorApp(x_51, x_26);
lean_dec(x_26);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_st_ref_get(x_6, x_50);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_3, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_61, x_8);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
case 4:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
case 5:
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
return x_68;
}
case 6:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_7);
return x_70;
}
default: 
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_dec(x_1);
x_1 = x_71;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_3 = x_7;
x_4 = x_9;
goto _start;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_11, 2);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_name_eq(x_12, x_13);
return x_14;
}
default: 
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_1, 4);
x_15 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_16 = l_panic___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases___spec__1(x_15);
x_17 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(x_16, x_13, x_14, x_10);
lean_dec(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_array_fget(x_8, x_10);
x_24 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(x_23, x_21, x_22, x_10);
lean_dec(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_array_uget(x_15, x_4);
x_27 = l_Lean_Compiler_LCNF_AltCore_getCode(x_16);
lean_dec(x_16);
x_28 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(x_27, x_6, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_17 = x_31;
x_18 = x_30;
goto block_26;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_name_eq(x_1, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_17 = x_35;
x_18 = x_32;
goto block_26;
}
else
{
lean_object* x_36; 
x_36 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2;
x_17 = x_36;
x_18 = x_32;
goto block_26;
}
}
block_26:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
x_11 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_65 = lean_array_get_size(x_8);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_69 = l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(x_68);
x_9 = x_69;
goto block_64;
}
else
{
lean_object* x_70; 
x_70 = lean_array_fget(x_8, x_66);
x_9 = x_70;
goto block_64;
}
block_64:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Compiler_LCNF_AltCore_getCode(x_9);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_20);
x_21 = l_Lean_Compiler_LCNF_getFunDecl(x_20, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases(x_22, x_2, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_array_get_size(x_8);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Array_toSubarray___rarg(x_8, x_35, x_34);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1(x_20, x_36, x_38, x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_20);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_42, 0);
lean_dec(x_53);
lean_ctor_set(x_43, 0, x_20);
return x_42;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
lean_ctor_set(x_43, 0, x_20);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_20);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_8);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_dec_lt(x_5, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_16 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_15);
x_17 = l_Lean_Compiler_LCNF_AltCore_getCode(x_16);
lean_dec(x_16);
lean_inc(x_3);
x_18 = l_Lean_Compiler_LCNF_Code_alphaEqv(x_17, x_3);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_23 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_23;
x_8 = x_22;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_array_fget(x_1, x_5);
x_26 = l_Lean_Compiler_LCNF_AltCore_getCode(x_25);
lean_dec(x_25);
lean_inc(x_3);
x_27 = l_Lean_Compiler_LCNF_Code_alphaEqv(x_26, x_3);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_32 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_32;
x_8 = x_31;
goto _start;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
if (x_4 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_8 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_7);
x_9 = l_Lean_Compiler_LCNF_AltCore_getCode(x_8);
lean_dec(x_8);
lean_inc(x_3);
x_10 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1(x_1, x_3, x_9, x_3, x_6, x_3, x_5, x_5);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_1, x_2);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_AltCore_getCode(x_11);
lean_dec(x_11);
lean_inc(x_3);
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1(x_1, x_3, x_12, x_3, x_6, x_3, x_5, x_5);
lean_dec(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_4);
x_16 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_4);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_nat_dec_lt(x_4, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_22 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_16);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget(x_1, x_4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_16);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_4);
x_30 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_4);
x_31 = lean_nat_dec_lt(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_33;
x_7 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_35 = lean_nat_dec_lt(x_4, x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_37 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_39;
x_7 = x_38;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_array_fget(x_1, x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_43;
x_7 = x_42;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_4);
x_16 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_4);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_nat_dec_lt(x_4, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_22 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_16);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget(x_1, x_4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_16);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_4);
x_30 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_4);
x_31 = lean_nat_dec_lt(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_33;
x_7 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_35 = lean_nat_dec_lt(x_4, x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_37 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_39;
x_7 = x_38;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_array_fget(x_1, x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_43;
x_7 = x_42;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
x_5 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_7 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_10 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1(x_1, x_2, x_2, x_9, x_2, x_9, x_8);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_array_fget(x_1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2(x_1, x_2, x_2, x_16, x_2, x_16, x_15);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Compiler.LCNF.Simp.0.Lean.Compiler.LCNF.Simp.addDefault", 69);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(785u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_14 = lean_array_uget(x_2, x_4);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = l_Lean_Compiler_LCNF_AltCore_getCode(x_14);
x_26 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_27 = l_Lean_Compiler_LCNF_Code_alphaEqv(x_25, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_push(x_23, x_14);
lean_ctor_set(x_5, 0, x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_5);
x_15 = x_30;
x_16 = x_11;
goto block_21;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_free_object(x_5);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 2);
lean_inc(x_32);
lean_dec(x_14);
x_33 = l_Lean_Compiler_LCNF_eraseParams(x_31, x_8, x_9, x_10, x_11);
lean_dec(x_31);
x_34 = lean_unbox(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_LCNF_eraseCode(x_32, x_8, x_9, x_10, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_24);
lean_dec(x_24);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(x_23, x_39, x_37, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_15 = x_41;
x_16 = x_42;
goto block_21;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_32);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_box(0);
x_45 = lean_unbox(x_24);
lean_dec(x_24);
x_46 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(x_23, x_45, x_44, x_6, x_7, x_8, x_9, x_10, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_15 = x_47;
x_16 = x_48;
goto block_21;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_14);
x_49 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1(x_49, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_5);
x_15 = x_52;
x_16 = x_51;
goto block_21;
}
else
{
uint8_t x_53; 
lean_free_object(x_5);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
x_59 = l_Lean_Compiler_LCNF_AltCore_getCode(x_14);
x_60 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_61 = l_Lean_Compiler_LCNF_Code_alphaEqv(x_59, x_60);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_array_push(x_57, x_14);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_15 = x_65;
x_16 = x_11;
goto block_21;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_14, 2);
lean_inc(x_67);
lean_dec(x_14);
x_68 = l_Lean_Compiler_LCNF_eraseParams(x_66, x_8, x_9, x_10, x_11);
lean_dec(x_66);
x_69 = lean_unbox(x_58);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_eraseCode(x_67, x_8, x_9, x_10, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_58);
lean_dec(x_58);
x_75 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(x_57, x_74, x_72, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_72);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_15 = x_76;
x_16 = x_77;
goto block_21;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_67);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_box(0);
x_80 = lean_unbox(x_58);
lean_dec(x_58);
x_81 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(x_57, x_80, x_79, x_6, x_7, x_8, x_9, x_10, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_15 = x_82;
x_16 = x_83;
goto block_21;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_14);
x_84 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_85 = l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1(x_84, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_57);
lean_ctor_set(x_87, 1, x_58);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_15 = x_88;
x_16 = x_86;
goto block_21;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_91 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
size_t x_6; size_t x_7; 
lean_dec(x_5);
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = 1;
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
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_array_get_size(x_1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_dec_le(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = lean_box(0);
x_8 = x_45;
goto block_39;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_40, x_40);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_40);
x_47 = lean_box(0);
x_8 = x_47;
goto block_39;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3(x_1, x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_8 = x_51;
goto block_39;
}
else
{
lean_object* x_52; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
block_39:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
x_9 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1;
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2(x_10, x_1, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_AltCore_getCode(x_10);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_push(x_23, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_LCNF_AltCore_getCode(x_10);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_findCtor(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l_Lean_Expr_constructorApp_x3f(x_17, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_8);
x_20 = lean_box(0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
uint8_t x_21; 
lean_free_object(x_13);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_16);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_nat_add(x_28, x_8);
lean_dec(x_8);
lean_dec(x_28);
x_30 = lean_array_get_size(x_24);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_24);
x_32 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_33 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_32);
lean_ctor_set(x_19, 0, x_33);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_34; 
x_34 = lean_array_fget(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_23, 3);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_nat_add(x_36, x_8);
lean_dec(x_8);
lean_dec(x_36);
x_38 = lean_array_get_size(x_24);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_24);
x_40 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_41 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_40);
lean_ctor_set(x_19, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_array_fget(x_24, x_37);
lean_dec(x_37);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_nat_add(x_51, x_8);
lean_dec(x_8);
lean_dec(x_51);
x_53 = lean_array_get_size(x_47);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_47);
x_55 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_56 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_47, x_52);
lean_dec(x_52);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_50)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_50;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_13, 0);
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_13);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = 0;
x_66 = l_Lean_Expr_constructorApp_x3f(x_64, x_11, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_63);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_71, 3);
lean_inc(x_76);
lean_dec(x_71);
x_77 = lean_nat_add(x_76, x_8);
lean_dec(x_8);
lean_dec(x_76);
x_78 = lean_array_get_size(x_72);
x_79 = lean_nat_dec_lt(x_77, x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_77);
lean_dec(x_72);
x_80 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_81 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_80);
if (lean_is_scalar(x_70)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_70;
}
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_array_fget(x_72, x_77);
lean_dec(x_77);
lean_dec(x_72);
if (lean_is_scalar(x_70)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_70;
}
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_75)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_75;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_74);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_7);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_isApp(x_1);
if (x_8 == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_9 = x_139;
x_10 = x_7;
goto block_138;
}
else
{
lean_object* x_140; 
x_140 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
x_9 = x_140;
x_10 = x_7;
goto block_138;
}
block_138:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = l_Lean_Expr_getAppFn(x_1);
x_16 = l_Lean_Expr_isFVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_19 = 1;
x_20 = l_Lean_Compiler_LCNF_Simp_findExpr(x_15, x_19, x_4, x_5, x_6, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Expr_isApp(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isConst(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_free_object(x_9);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_free_object(x_20);
x_27 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_30);
x_32 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_35);
x_37 = l_Lean_mkAppN(x_22, x_36);
lean_ctor_set(x_9, 0, x_37);
lean_ctor_set(x_27, 0, x_9);
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_40);
x_42 = lean_mk_array(x_40, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_40, x_43);
lean_dec(x_40);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_42, x_44);
x_46 = l_Lean_mkAppN(x_22, x_45);
lean_ctor_set(x_9, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_20);
x_48 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_23);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_51);
x_53 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_54, x_56);
x_58 = l_Lean_mkAppN(x_22, x_57);
lean_ctor_set(x_9, 0, x_58);
lean_ctor_set(x_48, 0, x_9);
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_62 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_61);
x_63 = lean_mk_array(x_61, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_61, x_64);
lean_dec(x_61);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = l_Lean_mkAppN(x_22, x_66);
lean_ctor_set(x_9, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_9);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_20, 0);
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_20);
x_71 = l_Lean_Expr_isApp(x_69);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = l_Lean_Expr_isConst(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_free_object(x_9);
lean_dec(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_70);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(0u);
x_79 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_78);
x_80 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_79);
x_81 = lean_mk_array(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_79, x_82);
lean_dec(x_79);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_81, x_83);
x_85 = l_Lean_mkAppN(x_69, x_84);
lean_ctor_set(x_9, 0, x_85);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_9);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_70);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_90);
x_92 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_91);
x_93 = lean_mk_array(x_91, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_91, x_94);
lean_dec(x_91);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_93, x_95);
x_97 = l_Lean_mkAppN(x_69, x_96);
lean_ctor_set(x_9, 0, x_97);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_9);
lean_ctor_set(x_98, 1, x_88);
return x_98;
}
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_9);
x_99 = l_Lean_Expr_getAppFn(x_1);
x_100 = l_Lean_Expr_isFVar(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_99);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_10);
return x_102;
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = 1;
x_104 = l_Lean_Compiler_LCNF_Simp_findExpr(x_99, x_103, x_4, x_5, x_6, x_10);
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
x_108 = l_Lean_Expr_isApp(x_105);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Expr_isConst(x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_105);
lean_dec(x_1);
x_110 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_107);
x_112 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_106);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_unsigned_to_nat(0u);
x_116 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_115);
x_117 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_116);
x_118 = lean_mk_array(x_116, x_117);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_116, x_119);
lean_dec(x_116);
x_121 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_118, x_120);
x_122 = l_Lean_mkAppN(x_105, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_is_scalar(x_114)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_114;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_113);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_107);
x_125 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_106);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_unsigned_to_nat(0u);
x_129 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_128);
x_130 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_129);
x_131 = lean_mk_array(x_129, x_130);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_sub(x_129, x_132);
lean_dec(x_129);
x_134 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_131, x_133);
x_135 = l_Lean_mkAppN(x_105, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
if (lean_is_scalar(x_127)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_127;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
return x_137;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_implementedByAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
if (x_9 == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_10 = x_93;
x_11 = x_7;
goto block_92;
}
else
{
lean_object* x_94; 
x_94 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
x_10 = x_94;
x_11 = x_7;
goto block_92;
}
block_92:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instInhabitedName;
x_23 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_24 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_22, x_23, x_21, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
uint8_t x_26; 
lean_free_object(x_17);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_20);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Expr_const___override(x_27, x_16);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_32);
x_34 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_33);
x_35 = lean_mk_array(x_33, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_33, x_36);
lean_dec(x_33);
x_38 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_35, x_37);
x_39 = l_Lean_mkAppN(x_31, x_38);
lean_ctor_set(x_24, 0, x_39);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = l_Lean_Expr_const___override(x_27, x_16);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_42);
x_44 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_43);
x_45 = lean_mk_array(x_43, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_43, x_46);
lean_dec(x_43);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_45, x_47);
x_49 = l_Lean_mkAppN(x_41, x_48);
lean_ctor_set(x_24, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_24, 0);
lean_inc(x_51);
lean_dec(x_24);
x_52 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_20);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Expr_const___override(x_51, x_16);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_56);
x_58 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_57);
x_59 = lean_mk_array(x_57, x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_57, x_60);
lean_dec(x_57);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_59, x_61);
x_63 = l_Lean_mkAppN(x_55, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_54)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_54;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_53);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_17, 0);
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_17);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instInhabitedName;
x_70 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_71 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_69, x_70, x_68, x_15);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_16);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_67);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = l_Lean_Expr_const___override(x_74, x_16);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_80);
x_82 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1;
lean_inc(x_81);
x_83 = lean_mk_array(x_81, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_81, x_84);
lean_dec(x_81);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_83, x_85);
x_87 = l_Lean_mkAppN(x_79, x_86);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_77);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_14);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_11);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_22 = x_12;
} else {
 lean_dec_ref(x_12);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_8, 0, x_29);
return x_8;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_32 = x_9;
} else {
 lean_dec_ref(x_9);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Compiler_LCNF_eraseLetDecl(x_1, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = l_Lean_Compiler_LCNF_eraseFunDecl(x_1, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2(x_20, x_2, x_3, x_4, x_5, x_6, x_11);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_environment_find(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2(x_35, x_2, x_3, x_4, x_5, x_6, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_38 = x_28;
} else {
 lean_dec_ref(x_28);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (x_9 == 0)
{
lean_object* x_266; 
x_266 = lean_box(0);
x_10 = x_266;
x_11 = x_7;
goto block_265;
}
else
{
lean_object* x_267; 
x_267 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
x_10 = x_267;
x_11 = x_7;
goto block_265;
}
block_265:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = l_Lean_Expr_getAppFn(x_14);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_ConstantInfo_type(x_21);
lean_dec(x_21);
x_23 = l_Lean_Compiler_LCNF_hasLocalInst(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_17);
lean_inc(x_16);
x_25 = l_Lean_Meta_isInstance(x_16, x_5, x_6, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_16, x_5, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_42);
x_44 = l_Lean_Compiler_LCNF_Decl_getArity(x_41);
lean_dec(x_41);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_free_object(x_30);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_29, 0, x_46);
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_29);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
x_48 = l_Lean_Compiler_LCNF_mkNewParams(x_47, x_4, x_5, x_6, x_38);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_get_size(x_49);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = 0;
lean_inc(x_49);
x_54 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_52, x_53, x_49);
x_55 = l_Lean_mkAppN(x_14, x_54);
x_56 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_57 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_55, x_56, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_64 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_49, x_62, x_63, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = l_Lean_Expr_fvar___override(x_68);
x_70 = l_Lean_Compiler_LCNF_Simp_addSubst(x_67, x_69, x_2, x_3, x_4, x_5, x_6, x_66);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_30, 0, x_65);
lean_ctor_set(x_72, 0, x_30);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_30, 0, x_65);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_free_object(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
return x_64;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_64, 0);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_64);
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
lean_dec(x_49);
lean_free_object(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_57);
if (x_81 == 0)
{
return x_57;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_57, 0);
x_83 = lean_ctor_get(x_57, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_57);
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
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_30, 0);
lean_inc(x_85);
lean_dec(x_30);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_86);
x_88 = l_Lean_Compiler_LCNF_Decl_getArity(x_85);
lean_dec(x_85);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = lean_box(0);
lean_ctor_set(x_29, 0, x_90);
return x_29;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_29);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = l_Lean_Compiler_LCNF_mkNewParams(x_91, x_4, x_5, x_6, x_38);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_array_get_size(x_93);
x_96 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_97 = 0;
lean_inc(x_93);
x_98 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_96, x_97, x_93);
x_99 = l_Lean_mkAppN(x_14, x_98);
x_100 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_101 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_99, x_100, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_93, x_106, x_107, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = l_Lean_Expr_fvar___override(x_112);
x_114 = l_Lean_Compiler_LCNF_Simp_addSubst(x_111, x_113, x_2, x_3, x_4, x_5, x_6, x_110);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_115);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_109);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_108, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_108, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_123 = x_108;
} else {
 lean_dec_ref(x_108);
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
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_93);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_125 = lean_ctor_get(x_101, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_101, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_127 = x_101;
} else {
 lean_dec_ref(x_101);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_29, 1);
lean_inc(x_129);
lean_dec(x_29);
x_130 = lean_ctor_get(x_30, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_131 = x_30;
} else {
 lean_dec_ref(x_30);
 x_131 = lean_box(0);
}
x_132 = lean_unsigned_to_nat(0u);
x_133 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_132);
x_134 = l_Lean_Compiler_LCNF_Decl_getArity(x_130);
lean_dec(x_130);
x_135 = lean_nat_dec_lt(x_133, x_134);
lean_dec(x_134);
lean_dec(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_131);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_129);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_138 = lean_ctor_get(x_1, 2);
lean_inc(x_138);
x_139 = l_Lean_Compiler_LCNF_mkNewParams(x_138, x_4, x_5, x_6, x_129);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_array_get_size(x_140);
x_143 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_144 = 0;
lean_inc(x_140);
x_145 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_143, x_144, x_140);
x_146 = l_Lean_mkAppN(x_14, x_145);
x_147 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_148 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_146, x_147, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_140, x_153, x_154, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = l_Lean_Expr_fvar___override(x_159);
x_161 = l_Lean_Compiler_LCNF_Simp_addSubst(x_158, x_160, x_2, x_3, x_4, x_5, x_6, x_157);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_131;
}
lean_ctor_set(x_166, 0, x_156);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_168 = lean_ctor_get(x_155, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_155, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_170 = x_155;
} else {
 lean_dec_ref(x_155);
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
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_140);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_172 = lean_ctor_get(x_148, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_148, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_174 = x_148;
} else {
 lean_dec_ref(x_148);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_29);
if (x_176 == 0)
{
return x_29;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_29, 0);
x_178 = lean_ctor_get(x_29, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_29);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_25);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_25, 0);
lean_dec(x_181);
x_182 = lean_box(0);
lean_ctor_set(x_25, 0, x_182);
return x_25;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_25, 1);
lean_inc(x_183);
lean_dec(x_25);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_17, 0);
x_187 = lean_ctor_get(x_17, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_17);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_ConstantInfo_type(x_188);
lean_dec(x_188);
x_190 = l_Lean_Compiler_LCNF_hasLocalInst(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_187);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_inc(x_16);
x_193 = l_Lean_Meta_isInstance(x_16, x_5, x_6, x_187);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_197 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_16, x_5, x_6, x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = lean_box(0);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_204 = x_197;
} else {
 lean_dec_ref(x_197);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(0u);
x_208 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_207);
x_209 = l_Lean_Compiler_LCNF_Decl_getArity(x_205);
lean_dec(x_205);
x_210 = lean_nat_dec_lt(x_208, x_209);
lean_dec(x_209);
lean_dec(x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_206);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_211 = lean_box(0);
if (lean_is_scalar(x_204)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_204;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_203);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_204);
x_213 = lean_ctor_get(x_1, 2);
lean_inc(x_213);
x_214 = l_Lean_Compiler_LCNF_mkNewParams(x_213, x_4, x_5, x_6, x_203);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_array_get_size(x_215);
x_218 = lean_usize_of_nat(x_217);
lean_dec(x_217);
x_219 = 0;
lean_inc(x_215);
x_220 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_218, x_219, x_215);
x_221 = l_Lean_mkAppN(x_14, x_220);
x_222 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_223 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_221, x_222, x_4, x_5, x_6, x_216);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_224);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_230 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_215, x_228, x_229, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_1, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
x_235 = l_Lean_Expr_fvar___override(x_234);
x_236 = l_Lean_Compiler_LCNF_Simp_addSubst(x_233, x_235, x_2, x_3, x_4, x_5, x_6, x_232);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_237);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_206;
}
lean_ctor_set(x_241, 0, x_231);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_243 = lean_ctor_get(x_230, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_230, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_245 = x_230;
} else {
 lean_dec_ref(x_230);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_215);
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_247 = lean_ctor_get(x_223, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_223, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_249 = x_223;
} else {
 lean_dec_ref(x_223);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_251 = lean_ctor_get(x_197, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_197, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_253 = x_197;
} else {
 lean_dec_ref(x_197);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_255 = lean_ctor_get(x_193, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_256 = x_193;
} else {
 lean_dec_ref(x_193);
 x_256 = lean_box(0);
}
x_257 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_255);
return x_258;
}
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_17);
if (x_259 == 0)
{
return x_17;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_17, 0);
x_261 = lean_ctor_get(x_17, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_17);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_11);
return x_264;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_8);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_1, x_15, x_4, x_5, x_6, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1;
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_8);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Compiler_LCNF_Simp_simp(x_20, x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_15, x_18, x_22, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_8);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_st_ref_get(x_6, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_22, x_16);
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_1, x_15, x_23, x_4, x_5, x_6, x_21);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1;
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__7(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_12 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = l_Lean_Expr_isFVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_17 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_4, x_1, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_15, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_23 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = l_Lean_Compiler_LCNF_Simp_isUsed(x_26, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
lean_inc(x_4);
x_37 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_41 = lean_ptr_addr(x_24);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_24);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_45 = lean_ptr_addr(x_4);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_3);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_24);
lean_ctor_set(x_37, 0, x_47);
return x_37;
}
else
{
lean_dec(x_24);
lean_dec(x_4);
lean_ctor_set(x_37, 0, x_3);
return x_37;
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_50 = lean_ptr_addr(x_24);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_24);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_55 = lean_ptr_addr(x_4);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_24);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_24);
lean_dec(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_48);
return x_59;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_21, 0);
lean_inc(x_64);
lean_dec(x_21);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_ctor_get(x_4, 0);
lean_inc(x_68);
x_69 = l_Lean_Expr_fvar___override(x_67);
x_70 = l_Lean_Compiler_LCNF_Simp_addSubst(x_68, x_69, x_6, x_7, x_8, x_9, x_10, x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_71);
lean_dec(x_4);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_74 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_66, x_75, x_6, x_7, x_8, x_9, x_10, x_76);
lean_dec(x_66);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_74);
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
uint8_t x_82; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_20);
if (x_82 == 0)
{
return x_20;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_20, 0);
x_84 = lean_ctor_get(x_20, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_20);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_17, 1);
lean_inc(x_86);
lean_dec(x_17);
x_87 = lean_ctor_get(x_18, 0);
lean_inc(x_87);
lean_dec(x_18);
x_88 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_86);
lean_dec(x_4);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Compiler_LCNF_Simp_simp(x_87, x_6, x_7, x_8, x_9, x_10, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_17);
if (x_91 == 0)
{
return x_17;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_17, 0);
x_93 = lean_ctor_get(x_17, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_17);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_ctor_get(x_4, 0);
lean_inc(x_95);
x_96 = l_Lean_Compiler_LCNF_Simp_addSubst(x_95, x_15, x_6, x_7, x_8, x_9, x_10, x_14);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_97);
lean_dec(x_4);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
lean_dec(x_12);
x_102 = lean_ctor_get(x_13, 0);
lean_inc(x_102);
lean_dec(x_13);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_1);
x_104 = l_Lean_Compiler_LCNF_Simp_simp(x_103, x_6, x_7, x_8, x_9, x_10, x_101);
return x_104;
}
}
else
{
uint8_t x_105; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_12);
if (x_105 == 0)
{
return x_12;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_12, 0);
x_107 = lean_ctor_get(x_12, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_12);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_1);
x_14 = lean_ptr_addr(x_2);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_4);
x_19 = lean_ptr_addr(x_3);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_14, x_5, x_2, x_3, x_27, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_30 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_14, x_5, x_2, x_3, x_31, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_apply_8(x_1, x_11, x_13, x_4, x_5, x_6, x_7, x_8, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_1);
x_14 = lean_ptr_addr(x_2);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_4);
x_19 = lean_ptr_addr(x_3);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_14, x_5, x_2, x_3, x_27, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_30 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_14, x_5, x_2, x_3, x_31, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_2, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp), 7, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed), 8, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(x_1, x_9, x_10, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_simp(x_16, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_19);
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
x_23 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_11);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_11);
lean_inc(x_4);
x_19 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_4, x_5, x_6, x_7, x_8, x_9, x_16);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_4);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__9), 8, 1);
lean_closure_set(x_22, 0, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_23 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(x_24, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_53; lean_object* x_54; lean_object* x_65; uint8_t x_66; 
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
x_53 = lean_array_get_size(x_28);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_dec_eq(x_53, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_53);
lean_dec(x_26);
x_67 = lean_box(0);
x_31 = x_67;
goto block_52;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_lt(x_68, x_53);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_71 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_71);
lean_dec(x_53);
lean_dec(x_26);
x_72 = lean_box(0);
x_31 = x_72;
goto block_52;
}
else
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_73 = lean_box(0);
x_54 = x_73;
goto block_64;
}
}
else
{
lean_object* x_74; 
x_74 = lean_array_fget(x_28, x_68);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_74);
lean_dec(x_53);
lean_dec(x_26);
x_75 = lean_box(0);
x_31 = x_75;
goto block_52;
}
else
{
lean_object* x_76; 
lean_dec(x_74);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = lean_box(0);
x_54 = x_76;
goto block_64;
}
}
}
block_52:
{
size_t x_32; size_t x_33; uint8_t x_34; 
lean_dec(x_31);
x_32 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_33 = lean_ptr_addr(x_28);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_3);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_4);
lean_ctor_set(x_36, 3, x_28);
x_37 = lean_alloc_ctor(4, 1, 0);
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
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_40 = lean_ptr_addr(x_18);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_18);
lean_ctor_set(x_43, 2, x_4);
lean_ctor_set(x_43, 3, x_28);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_30)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_30;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_name_eq(x_2, x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_18);
lean_ctor_set(x_48, 2, x_4);
lean_ctor_set(x_48, 3, x_28);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_30)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_30;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_29);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_30)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_30;
}
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
}
block_64:
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_54);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_lt(x_55, x_53);
lean_dec(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_28);
x_57 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_58 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_57);
x_59 = l_Lean_Compiler_LCNF_AltCore_getCode(x_58);
lean_dec(x_58);
if (lean_is_scalar(x_26)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_26;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_29);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_array_fget(x_28, x_55);
lean_dec(x_28);
x_62 = l_Lean_Compiler_LCNF_AltCore_getCode(x_61);
lean_dec(x_61);
if (lean_is_scalar(x_26)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_26;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_29);
return x_63;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_27);
if (x_77 == 0)
{
return x_27;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_27, 0);
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_27);
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
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_23);
if (x_81 == 0)
{
return x_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_23, 0);
x_83 = lean_ctor_get(x_23, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_23);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 10);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_11, x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_5, 10);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 9);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 8);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_33);
x_34 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_7);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_36, x_2, x_3, x_4, x_5, x_6, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 3);
lean_inc(x_41);
x_42 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_41, x_2, x_3, x_4, x_5, x_6, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_37, x_36, x_1, x_39, x_45, x_2, x_3, x_4, x_5, x_6, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_39, x_48, x_4, x_5, x_6, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_37, x_36, x_1, x_50, x_52, x_2, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
}
case 1:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_57, x_2, x_3, x_4, x_5, x_6, x_54);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_1);
lean_inc(x_55);
x_62 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 12, 4);
lean_closure_set(x_62, 0, x_56);
lean_closure_set(x_62, 1, x_55);
lean_closure_set(x_62, 2, x_1);
lean_closure_set(x_62, 3, x_59);
x_63 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
x_65 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_62, x_55, x_64, x_2, x_3, x_4, x_5, x_6, x_61);
return x_65;
}
else
{
lean_object* x_66; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_66 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_55, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
x_70 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_62, x_67, x_69, x_2, x_3, x_4, x_5, x_6, x_68);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_62);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = lean_st_ref_get(x_6, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_3, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_55);
x_82 = l_Lean_Compiler_LCNF_normFunDeclImp(x_55, x_81, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_box(0);
x_86 = lean_unbox(x_59);
lean_dec(x_59);
x_87 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_56, x_55, x_1, x_86, x_83, x_85, x_2, x_3, x_4, x_5, x_6, x_84);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_82);
if (x_88 == 0)
{
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
case 2:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_34, 1);
lean_inc(x_92);
lean_dec(x_34);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_95, x_2, x_3, x_4, x_5, x_6, x_92);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
lean_inc(x_1);
lean_inc(x_93);
x_100 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 12, 4);
lean_closure_set(x_100, 0, x_94);
lean_closure_set(x_100, 1, x_93);
lean_closure_set(x_100, 2, x_1);
lean_closure_set(x_100, 3, x_97);
x_101 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_box(0);
x_103 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_100, x_93, x_102, x_2, x_3, x_4, x_5, x_6, x_99);
return x_103;
}
else
{
lean_object* x_104; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_104 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_93, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_box(0);
x_108 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_100, x_105, x_107, x_2, x_3, x_4, x_5, x_6, x_106);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_100);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_96, 1);
lean_inc(x_113);
lean_dec(x_96);
x_114 = lean_st_ref_get(x_6, x_113);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_get(x_3, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_93);
x_120 = l_Lean_Compiler_LCNF_normFunDeclImp(x_93, x_119, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = lean_unbox(x_97);
lean_dec(x_97);
x_125 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_94, x_93, x_1, x_124, x_121, x_123, x_2, x_3, x_4, x_5, x_6, x_122);
return x_125;
}
else
{
uint8_t x_126; 
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_120);
if (x_126 == 0)
{
return x_120;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_120, 0);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_120);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
case 3:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_34, 1);
lean_inc(x_130);
lean_dec(x_34);
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
x_133 = lean_st_ref_get(x_6, x_130);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_get(x_3, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_131);
x_139 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_138, x_131);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_132);
x_140 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_132, x_2, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_163; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_141);
lean_inc(x_139);
x_163 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_139, x_141, x_2, x_3, x_4, x_5, x_6, x_142);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_139);
x_166 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_139, x_2, x_3, x_4, x_5, x_6, x_165);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_array_get_size(x_141);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_nat_dec_lt(x_169, x_168);
if (x_170 == 0)
{
lean_dec(x_168);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = x_167;
goto block_162;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_168, x_168);
if (x_171 == 0)
{
lean_dec(x_168);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = x_167;
goto block_162;
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = 0;
x_173 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_174 = lean_box(0);
x_175 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_141, x_172, x_173, x_174, x_2, x_3, x_4, x_5, x_6, x_167);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_144 = x_176;
goto block_162;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_1);
x_177 = lean_ctor_get(x_163, 1);
lean_inc(x_177);
lean_dec(x_163);
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
lean_dec(x_164);
x_1 = x_178;
x_7 = x_177;
goto _start;
}
}
else
{
uint8_t x_180; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_163);
if (x_180 == 0)
{
return x_163;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_163, 0);
x_182 = lean_ctor_get(x_163, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_163);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
block_162:
{
uint8_t x_145; 
x_145 = lean_name_eq(x_131, x_139);
lean_dec(x_131);
if (x_145 == 0)
{
uint8_t x_146; 
lean_dec(x_132);
x_146 = !lean_is_exclusive(x_1);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_1, 1);
lean_dec(x_147);
x_148 = lean_ctor_get(x_1, 0);
lean_dec(x_148);
lean_ctor_set(x_1, 1, x_141);
lean_ctor_set(x_1, 0, x_139);
if (lean_is_scalar(x_143)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_143;
}
lean_ctor_set(x_149, 0, x_1);
lean_ctor_set(x_149, 1, x_144);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_1);
x_150 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_141);
if (lean_is_scalar(x_143)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_143;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_144);
return x_151;
}
}
else
{
size_t x_152; size_t x_153; uint8_t x_154; 
x_152 = lean_ptr_addr(x_132);
lean_dec(x_132);
x_153 = lean_ptr_addr(x_141);
x_154 = lean_usize_dec_eq(x_152, x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_1, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 0);
lean_dec(x_157);
lean_ctor_set(x_1, 1, x_141);
lean_ctor_set(x_1, 0, x_139);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_144);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_1);
x_159 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_159, 0, x_139);
lean_ctor_set(x_159, 1, x_141);
if (lean_is_scalar(x_143)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_143;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_144);
return x_160;
}
}
else
{
lean_object* x_161; 
lean_dec(x_141);
lean_dec(x_139);
if (lean_is_scalar(x_143)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_143;
}
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_144);
return x_161;
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_139);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_140);
if (x_184 == 0)
{
return x_140;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_140, 0);
x_186 = lean_ctor_get(x_140, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_140);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
case 4:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_34, 1);
lean_inc(x_188);
lean_dec(x_34);
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_189);
x_190 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_189, x_2, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 3);
lean_inc(x_196);
lean_inc(x_195);
x_197 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 8, 1);
lean_closure_set(x_197, 0, x_195);
x_198 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_199 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_199, 0, x_198);
lean_closure_set(x_199, 1, x_197);
lean_inc(x_1);
lean_inc(x_195);
lean_inc(x_189);
x_200 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed), 10, 3);
lean_closure_set(x_200, 0, x_189);
lean_closure_set(x_200, 1, x_195);
lean_closure_set(x_200, 2, x_1);
x_201 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_201, 0, x_199);
lean_closure_set(x_201, 1, x_200);
lean_inc(x_189);
x_202 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(x_189, x_2, x_3, x_4, x_5, x_6, x_192);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_203 = x_189;
} else {
 lean_dec_ref(x_189);
 x_203 = lean_box(0);
}
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_201);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_st_ref_get(x_6, x_205);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_st_ref_get(x_3, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_195);
x_212 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_211, x_195);
x_213 = lean_st_ref_get(x_6, x_210);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_st_ref_get(x_3, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_194);
x_219 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_218, x_194);
lean_inc(x_212);
x_220 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_212, x_2, x_3, x_4, x_5, x_6, x_217);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
lean_inc(x_212);
x_222 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__9), 8, 1);
lean_closure_set(x_222, 0, x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_196);
x_223 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_196, x_222, x_2, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(x_224, x_2, x_3, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_262; lean_object* x_263; uint8_t x_274; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_262 = lean_array_get_size(x_228);
x_274 = lean_nat_dec_eq(x_262, x_32);
if (x_274 == 0)
{
lean_object* x_275; 
lean_dec(x_262);
lean_dec(x_226);
x_275 = lean_box(0);
x_231 = x_275;
goto block_261;
}
else
{
lean_object* x_276; uint8_t x_277; 
x_276 = lean_unsigned_to_nat(0u);
x_277 = lean_nat_dec_lt(x_276, x_262);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_279 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
lean_dec(x_279);
lean_dec(x_262);
lean_dec(x_226);
x_280 = lean_box(0);
x_231 = x_280;
goto block_261;
}
else
{
lean_object* x_281; 
lean_dec(x_279);
lean_dec(x_230);
lean_dec(x_219);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_1);
x_281 = lean_box(0);
x_263 = x_281;
goto block_273;
}
}
else
{
lean_object* x_282; 
x_282 = lean_array_fget(x_228, x_276);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
lean_dec(x_282);
lean_dec(x_262);
lean_dec(x_226);
x_283 = lean_box(0);
x_231 = x_283;
goto block_261;
}
else
{
lean_object* x_284; 
lean_dec(x_282);
lean_dec(x_230);
lean_dec(x_219);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_1);
x_284 = lean_box(0);
x_263 = x_284;
goto block_273;
}
}
}
block_261:
{
size_t x_232; size_t x_233; uint8_t x_234; 
lean_dec(x_231);
x_232 = lean_ptr_addr(x_196);
lean_dec(x_196);
x_233 = lean_ptr_addr(x_228);
x_234 = lean_usize_dec_eq(x_232, x_233);
if (x_234 == 0)
{
uint8_t x_235; 
lean_dec(x_195);
lean_dec(x_194);
x_235 = !lean_is_exclusive(x_1);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_1, 0);
lean_dec(x_236);
if (lean_is_scalar(x_203)) {
 x_237 = lean_alloc_ctor(0, 4, 0);
} else {
 x_237 = x_203;
}
lean_ctor_set(x_237, 0, x_193);
lean_ctor_set(x_237, 1, x_219);
lean_ctor_set(x_237, 2, x_212);
lean_ctor_set(x_237, 3, x_228);
lean_ctor_set(x_1, 0, x_237);
if (lean_is_scalar(x_230)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_230;
}
lean_ctor_set(x_238, 0, x_1);
lean_ctor_set(x_238, 1, x_229);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_1);
if (lean_is_scalar(x_203)) {
 x_239 = lean_alloc_ctor(0, 4, 0);
} else {
 x_239 = x_203;
}
lean_ctor_set(x_239, 0, x_193);
lean_ctor_set(x_239, 1, x_219);
lean_ctor_set(x_239, 2, x_212);
lean_ctor_set(x_239, 3, x_228);
x_240 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_230)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_230;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_229);
return x_241;
}
}
else
{
size_t x_242; size_t x_243; uint8_t x_244; 
x_242 = lean_ptr_addr(x_194);
lean_dec(x_194);
x_243 = lean_ptr_addr(x_219);
x_244 = lean_usize_dec_eq(x_242, x_243);
if (x_244 == 0)
{
uint8_t x_245; 
lean_dec(x_195);
x_245 = !lean_is_exclusive(x_1);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_1, 0);
lean_dec(x_246);
if (lean_is_scalar(x_203)) {
 x_247 = lean_alloc_ctor(0, 4, 0);
} else {
 x_247 = x_203;
}
lean_ctor_set(x_247, 0, x_193);
lean_ctor_set(x_247, 1, x_219);
lean_ctor_set(x_247, 2, x_212);
lean_ctor_set(x_247, 3, x_228);
lean_ctor_set(x_1, 0, x_247);
if (lean_is_scalar(x_230)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_230;
}
lean_ctor_set(x_248, 0, x_1);
lean_ctor_set(x_248, 1, x_229);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_1);
if (lean_is_scalar(x_203)) {
 x_249 = lean_alloc_ctor(0, 4, 0);
} else {
 x_249 = x_203;
}
lean_ctor_set(x_249, 0, x_193);
lean_ctor_set(x_249, 1, x_219);
lean_ctor_set(x_249, 2, x_212);
lean_ctor_set(x_249, 3, x_228);
x_250 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_250, 0, x_249);
if (lean_is_scalar(x_230)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_230;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_229);
return x_251;
}
}
else
{
uint8_t x_252; 
x_252 = lean_name_eq(x_195, x_212);
lean_dec(x_195);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_1);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_1, 0);
lean_dec(x_254);
if (lean_is_scalar(x_203)) {
 x_255 = lean_alloc_ctor(0, 4, 0);
} else {
 x_255 = x_203;
}
lean_ctor_set(x_255, 0, x_193);
lean_ctor_set(x_255, 1, x_219);
lean_ctor_set(x_255, 2, x_212);
lean_ctor_set(x_255, 3, x_228);
lean_ctor_set(x_1, 0, x_255);
if (lean_is_scalar(x_230)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_230;
}
lean_ctor_set(x_256, 0, x_1);
lean_ctor_set(x_256, 1, x_229);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_1);
if (lean_is_scalar(x_203)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_203;
}
lean_ctor_set(x_257, 0, x_193);
lean_ctor_set(x_257, 1, x_219);
lean_ctor_set(x_257, 2, x_212);
lean_ctor_set(x_257, 3, x_228);
x_258 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_258, 0, x_257);
if (lean_is_scalar(x_230)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_230;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_229);
return x_259;
}
}
else
{
lean_object* x_260; 
lean_dec(x_228);
lean_dec(x_219);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_193);
if (lean_is_scalar(x_230)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_230;
}
lean_ctor_set(x_260, 0, x_1);
lean_ctor_set(x_260, 1, x_229);
return x_260;
}
}
}
}
block_273:
{
lean_object* x_264; uint8_t x_265; 
lean_dec(x_263);
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_nat_dec_lt(x_264, x_262);
lean_dec(x_262);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_228);
x_266 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_267 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_266);
x_268 = l_Lean_Compiler_LCNF_AltCore_getCode(x_267);
lean_dec(x_267);
if (lean_is_scalar(x_226)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_226;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_229);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_array_fget(x_228, x_264);
lean_dec(x_228);
x_271 = l_Lean_Compiler_LCNF_AltCore_getCode(x_270);
lean_dec(x_270);
if (lean_is_scalar(x_226)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_226;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_229);
return x_272;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_226);
lean_dec(x_219);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_227);
if (x_285 == 0)
{
return x_227;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_227, 0);
x_287 = lean_ctor_get(x_227, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_227);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_219);
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_223);
if (x_289 == 0)
{
return x_223;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_223, 0);
x_291 = lean_ctor_get(x_223, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_223);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_203);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_1);
x_293 = lean_ctor_get(x_202, 1);
lean_inc(x_293);
lean_dec(x_202);
x_294 = lean_ctor_get(x_204, 0);
lean_inc(x_294);
lean_dec(x_204);
x_295 = l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(x_294, x_201, x_2, x_3, x_4, x_5, x_6, x_293);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_202);
if (x_296 == 0)
{
return x_202;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_202, 0);
x_298 = lean_ctor_get(x_202, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_202);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_189);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_190);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_190, 0);
lean_dec(x_301);
x_302 = lean_ctor_get(x_191, 0);
lean_inc(x_302);
lean_dec(x_191);
lean_ctor_set(x_190, 0, x_302);
return x_190;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_190, 1);
lean_inc(x_303);
lean_dec(x_190);
x_304 = lean_ctor_get(x_191, 0);
lean_inc(x_304);
lean_dec(x_191);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_189);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_190);
if (x_306 == 0)
{
return x_190;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_190, 0);
x_308 = lean_ctor_get(x_190, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_190);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
case 5:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_310 = lean_ctor_get(x_34, 1);
lean_inc(x_310);
lean_dec(x_34);
x_311 = lean_ctor_get(x_1, 0);
lean_inc(x_311);
x_312 = lean_st_ref_get(x_6, x_310);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_st_ref_get(x_3, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
lean_inc(x_311);
x_318 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_317, x_311);
lean_inc(x_318);
x_319 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_318, x_2, x_3, x_4, x_5, x_6, x_316);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_319, 0);
lean_dec(x_321);
x_322 = lean_name_eq(x_311, x_318);
lean_dec(x_311);
if (x_322 == 0)
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_1);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_1, 0);
lean_dec(x_324);
lean_ctor_set(x_1, 0, x_318);
lean_ctor_set(x_319, 0, x_1);
return x_319;
}
else
{
lean_object* x_325; 
lean_dec(x_1);
x_325 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_325, 0, x_318);
lean_ctor_set(x_319, 0, x_325);
return x_319;
}
}
else
{
lean_dec(x_318);
lean_ctor_set(x_319, 0, x_1);
return x_319;
}
}
else
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_319, 1);
lean_inc(x_326);
lean_dec(x_319);
x_327 = lean_name_eq(x_311, x_318);
lean_dec(x_311);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_328 = x_1;
} else {
 lean_dec_ref(x_1);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(5, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_318);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_326);
return x_330;
}
else
{
lean_object* x_331; 
lean_dec(x_318);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_1);
lean_ctor_set(x_331, 1, x_326);
return x_331;
}
}
}
default: 
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_332 = lean_ctor_get(x_34, 1);
lean_inc(x_332);
lean_dec(x_34);
x_333 = lean_ctor_get(x_1, 0);
lean_inc(x_333);
x_334 = lean_st_ref_get(x_6, x_332);
lean_dec(x_6);
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
lean_dec(x_334);
x_336 = lean_st_ref_get(x_3, x_335);
lean_dec(x_3);
x_337 = !lean_is_exclusive(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; size_t x_341; size_t x_342; uint8_t x_343; 
x_338 = lean_ctor_get(x_336, 0);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec(x_338);
lean_inc(x_333);
x_340 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_339, x_333);
x_341 = lean_ptr_addr(x_333);
lean_dec(x_333);
x_342 = lean_ptr_addr(x_340);
x_343 = lean_usize_dec_eq(x_341, x_342);
if (x_343 == 0)
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_1);
if (x_344 == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_1, 0);
lean_dec(x_345);
lean_ctor_set(x_1, 0, x_340);
lean_ctor_set(x_336, 0, x_1);
return x_336;
}
else
{
lean_object* x_346; 
lean_dec(x_1);
x_346 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_346, 0, x_340);
lean_ctor_set(x_336, 0, x_346);
return x_336;
}
}
else
{
lean_dec(x_340);
lean_ctor_set(x_336, 0, x_1);
return x_336;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; size_t x_351; size_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_336, 0);
x_348 = lean_ctor_get(x_336, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_336);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
lean_dec(x_347);
lean_inc(x_333);
x_350 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_349, x_333);
x_351 = lean_ptr_addr(x_333);
lean_dec(x_333);
x_352 = lean_ptr_addr(x_350);
x_353 = lean_usize_dec_eq(x_351, x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_354 = x_1;
} else {
 lean_dec_ref(x_1);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(6, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_350);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_348);
return x_356;
}
else
{
lean_object* x_357; 
lean_dec(x_350);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_1);
lean_ctor_set(x_357, 1, x_348);
return x_357;
}
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_5);
x_358 = lean_unsigned_to_nat(1u);
x_359 = lean_nat_add(x_11, x_358);
lean_dec(x_11);
x_360 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_360, 0, x_8);
lean_ctor_set(x_360, 1, x_9);
lean_ctor_set(x_360, 2, x_10);
lean_ctor_set(x_360, 3, x_359);
lean_ctor_set(x_360, 4, x_12);
lean_ctor_set(x_360, 5, x_13);
lean_ctor_set(x_360, 6, x_14);
lean_ctor_set(x_360, 7, x_15);
lean_ctor_set(x_360, 8, x_16);
lean_ctor_set(x_360, 9, x_17);
lean_ctor_set(x_360, 10, x_18);
x_361 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_360, x_6, x_7);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_ctor_get(x_1, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_1, 1);
lean_inc(x_364);
lean_inc(x_363);
x_365 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_363, x_2, x_3, x_4, x_360, x_6, x_362);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
x_369 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_368, x_2, x_3, x_4, x_360, x_6, x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_box(0);
x_373 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_364, x_363, x_1, x_366, x_372, x_2, x_3, x_4, x_360, x_6, x_371);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
lean_dec(x_369);
x_375 = lean_ctor_get(x_370, 0);
lean_inc(x_375);
lean_dec(x_370);
x_376 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_366, x_375, x_4, x_360, x_6, x_374);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_box(0);
x_380 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_364, x_363, x_1, x_377, x_379, x_2, x_3, x_4, x_360, x_6, x_378);
return x_380;
}
}
case 1:
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_381 = lean_ctor_get(x_361, 1);
lean_inc(x_381);
lean_dec(x_361);
x_382 = lean_ctor_get(x_1, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_1, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
x_385 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_384, x_2, x_3, x_4, x_360, x_6, x_381);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_unbox(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
lean_inc(x_1);
lean_inc(x_382);
x_389 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 12, 4);
lean_closure_set(x_389, 0, x_383);
lean_closure_set(x_389, 1, x_382);
lean_closure_set(x_389, 2, x_1);
lean_closure_set(x_389, 3, x_386);
x_390 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_box(0);
x_392 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_389, x_382, x_391, x_2, x_3, x_4, x_360, x_6, x_388);
return x_392;
}
else
{
lean_object* x_393; 
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
x_393 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_382, x_4, x_360, x_6, x_388);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_box(0);
x_397 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_389, x_394, x_396, x_2, x_3, x_4, x_360, x_6, x_395);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_389);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_398 = lean_ctor_get(x_393, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_393, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_400 = x_393;
} else {
 lean_dec_ref(x_393);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_402 = lean_ctor_get(x_385, 1);
lean_inc(x_402);
lean_dec(x_385);
x_403 = lean_st_ref_get(x_6, x_402);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_405 = lean_st_ref_get(x_3, x_404);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
lean_dec(x_406);
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_382);
x_409 = l_Lean_Compiler_LCNF_normFunDeclImp(x_382, x_408, x_4, x_360, x_6, x_407);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_box(0);
x_413 = lean_unbox(x_386);
lean_dec(x_386);
x_414 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_383, x_382, x_1, x_413, x_410, x_412, x_2, x_3, x_4, x_360, x_6, x_411);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_386);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_415 = lean_ctor_get(x_409, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_409, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_417 = x_409;
} else {
 lean_dec_ref(x_409);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
}
case 2:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_419 = lean_ctor_get(x_361, 1);
lean_inc(x_419);
lean_dec(x_361);
x_420 = lean_ctor_get(x_1, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_1, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_422, x_2, x_3, x_4, x_360, x_6, x_419);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_unbox(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
lean_inc(x_1);
lean_inc(x_420);
x_427 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 12, 4);
lean_closure_set(x_427, 0, x_421);
lean_closure_set(x_427, 1, x_420);
lean_closure_set(x_427, 2, x_1);
lean_closure_set(x_427, 3, x_424);
x_428 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_box(0);
x_430 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_427, x_420, x_429, x_2, x_3, x_4, x_360, x_6, x_426);
return x_430;
}
else
{
lean_object* x_431; 
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
x_431 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_420, x_4, x_360, x_6, x_426);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_box(0);
x_435 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_427, x_432, x_434, x_2, x_3, x_4, x_360, x_6, x_433);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_427);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_436 = lean_ctor_get(x_431, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_431, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_438 = x_431;
} else {
 lean_dec_ref(x_431);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_440 = lean_ctor_get(x_423, 1);
lean_inc(x_440);
lean_dec(x_423);
x_441 = lean_st_ref_get(x_6, x_440);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_st_ref_get(x_3, x_442);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
lean_dec(x_444);
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_420);
x_447 = l_Lean_Compiler_LCNF_normFunDeclImp(x_420, x_446, x_4, x_360, x_6, x_445);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_box(0);
x_451 = lean_unbox(x_424);
lean_dec(x_424);
x_452 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_421, x_420, x_1, x_451, x_448, x_450, x_2, x_3, x_4, x_360, x_6, x_449);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_424);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_453 = lean_ctor_get(x_447, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_447, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_455 = x_447;
} else {
 lean_dec_ref(x_447);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
}
case 3:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_457 = lean_ctor_get(x_361, 1);
lean_inc(x_457);
lean_dec(x_361);
x_458 = lean_ctor_get(x_1, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_1, 1);
lean_inc(x_459);
x_460 = lean_st_ref_get(x_6, x_457);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_st_ref_get(x_3, x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_458);
x_466 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_465, x_458);
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_459);
x_467 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_459, x_2, x_3, x_4, x_360, x_6, x_464);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_484; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_468);
lean_inc(x_466);
x_484 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_466, x_468, x_2, x_3, x_4, x_360, x_6, x_469);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
lean_inc(x_466);
x_487 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_466, x_2, x_3, x_4, x_360, x_6, x_486);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
x_489 = lean_array_get_size(x_468);
x_490 = lean_unsigned_to_nat(0u);
x_491 = lean_nat_dec_lt(x_490, x_489);
if (x_491 == 0)
{
lean_dec(x_489);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_471 = x_488;
goto block_483;
}
else
{
uint8_t x_492; 
x_492 = lean_nat_dec_le(x_489, x_489);
if (x_492 == 0)
{
lean_dec(x_489);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_471 = x_488;
goto block_483;
}
else
{
size_t x_493; size_t x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_493 = 0;
x_494 = lean_usize_of_nat(x_489);
lean_dec(x_489);
x_495 = lean_box(0);
x_496 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_468, x_493, x_494, x_495, x_2, x_3, x_4, x_360, x_6, x_488);
lean_dec(x_6);
lean_dec(x_360);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_471 = x_497;
goto block_483;
}
}
}
else
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_466);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_1);
x_498 = lean_ctor_get(x_484, 1);
lean_inc(x_498);
lean_dec(x_484);
x_499 = lean_ctor_get(x_485, 0);
lean_inc(x_499);
lean_dec(x_485);
x_1 = x_499;
x_5 = x_360;
x_7 = x_498;
goto _start;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_466);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_501 = lean_ctor_get(x_484, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_484, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_503 = x_484;
} else {
 lean_dec_ref(x_484);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
block_483:
{
uint8_t x_472; 
x_472 = lean_name_eq(x_458, x_466);
lean_dec(x_458);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_473 = x_1;
} else {
 lean_dec_ref(x_1);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(3, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_466);
lean_ctor_set(x_474, 1, x_468);
if (lean_is_scalar(x_470)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_470;
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_471);
return x_475;
}
else
{
size_t x_476; size_t x_477; uint8_t x_478; 
x_476 = lean_ptr_addr(x_459);
lean_dec(x_459);
x_477 = lean_ptr_addr(x_468);
x_478 = lean_usize_dec_eq(x_476, x_477);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_479 = x_1;
} else {
 lean_dec_ref(x_1);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(3, 2, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_466);
lean_ctor_set(x_480, 1, x_468);
if (lean_is_scalar(x_470)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_470;
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_471);
return x_481;
}
else
{
lean_object* x_482; 
lean_dec(x_468);
lean_dec(x_466);
if (lean_is_scalar(x_470)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_470;
}
lean_ctor_set(x_482, 0, x_1);
lean_ctor_set(x_482, 1, x_471);
return x_482;
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_466);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_505 = lean_ctor_get(x_467, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_467, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_507 = x_467;
} else {
 lean_dec_ref(x_467);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
case 4:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_361, 1);
lean_inc(x_509);
lean_dec(x_361);
x_510 = lean_ctor_get(x_1, 0);
lean_inc(x_510);
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_510);
x_511 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_510, x_2, x_3, x_4, x_360, x_6, x_509);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_ctor_get(x_510, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_510, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_510, 2);
lean_inc(x_516);
x_517 = lean_ctor_get(x_510, 3);
lean_inc(x_517);
lean_inc(x_516);
x_518 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 8, 1);
lean_closure_set(x_518, 0, x_516);
x_519 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_520 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_520, 0, x_519);
lean_closure_set(x_520, 1, x_518);
lean_inc(x_1);
lean_inc(x_516);
lean_inc(x_510);
x_521 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed), 10, 3);
lean_closure_set(x_521, 0, x_510);
lean_closure_set(x_521, 1, x_516);
lean_closure_set(x_521, 2, x_1);
x_522 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_522, 0, x_520);
lean_closure_set(x_522, 1, x_521);
lean_inc(x_510);
x_523 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(x_510, x_2, x_3, x_4, x_360, x_6, x_513);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 lean_ctor_release(x_510, 2);
 lean_ctor_release(x_510, 3);
 x_524 = x_510;
} else {
 lean_dec_ref(x_510);
 x_524 = lean_box(0);
}
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_522);
x_526 = lean_ctor_get(x_523, 1);
lean_inc(x_526);
lean_dec(x_523);
x_527 = lean_st_ref_get(x_6, x_526);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
lean_dec(x_527);
x_529 = lean_st_ref_get(x_3, x_528);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_ctor_get(x_530, 0);
lean_inc(x_532);
lean_dec(x_530);
lean_inc(x_516);
x_533 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_532, x_516);
x_534 = lean_st_ref_get(x_6, x_531);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_st_ref_get(x_3, x_535);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get(x_537, 0);
lean_inc(x_539);
lean_dec(x_537);
lean_inc(x_515);
x_540 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_539, x_515);
lean_inc(x_533);
x_541 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_533, x_2, x_3, x_4, x_360, x_6, x_538);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec(x_541);
lean_inc(x_533);
x_543 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__9), 8, 1);
lean_closure_set(x_543, 0, x_533);
lean_inc(x_6);
lean_inc(x_360);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_517);
x_544 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_517, x_543, x_2, x_3, x_4, x_360, x_6, x_542);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_547 = x_544;
} else {
 lean_dec_ref(x_544);
 x_547 = lean_box(0);
}
x_548 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(x_545, x_2, x_3, x_4, x_360, x_6, x_546);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_574; lean_object* x_575; uint8_t x_586; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_551 = x_548;
} else {
 lean_dec_ref(x_548);
 x_551 = lean_box(0);
}
x_574 = lean_array_get_size(x_549);
x_586 = lean_nat_dec_eq(x_574, x_358);
if (x_586 == 0)
{
lean_object* x_587; 
lean_dec(x_574);
lean_dec(x_547);
x_587 = lean_box(0);
x_552 = x_587;
goto block_573;
}
else
{
lean_object* x_588; uint8_t x_589; 
x_588 = lean_unsigned_to_nat(0u);
x_589 = lean_nat_dec_lt(x_588, x_574);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
x_590 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_591 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_590);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; 
lean_dec(x_591);
lean_dec(x_574);
lean_dec(x_547);
x_592 = lean_box(0);
x_552 = x_592;
goto block_573;
}
else
{
lean_object* x_593; 
lean_dec(x_591);
lean_dec(x_551);
lean_dec(x_540);
lean_dec(x_533);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_1);
x_593 = lean_box(0);
x_575 = x_593;
goto block_585;
}
}
else
{
lean_object* x_594; 
x_594 = lean_array_fget(x_549, x_588);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; 
lean_dec(x_594);
lean_dec(x_574);
lean_dec(x_547);
x_595 = lean_box(0);
x_552 = x_595;
goto block_573;
}
else
{
lean_object* x_596; 
lean_dec(x_594);
lean_dec(x_551);
lean_dec(x_540);
lean_dec(x_533);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_1);
x_596 = lean_box(0);
x_575 = x_596;
goto block_585;
}
}
}
block_573:
{
size_t x_553; size_t x_554; uint8_t x_555; 
lean_dec(x_552);
x_553 = lean_ptr_addr(x_517);
lean_dec(x_517);
x_554 = lean_ptr_addr(x_549);
x_555 = lean_usize_dec_eq(x_553, x_554);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_516);
lean_dec(x_515);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_556 = x_1;
} else {
 lean_dec_ref(x_1);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_557 = lean_alloc_ctor(0, 4, 0);
} else {
 x_557 = x_524;
}
lean_ctor_set(x_557, 0, x_514);
lean_ctor_set(x_557, 1, x_540);
lean_ctor_set(x_557, 2, x_533);
lean_ctor_set(x_557, 3, x_549);
if (lean_is_scalar(x_556)) {
 x_558 = lean_alloc_ctor(4, 1, 0);
} else {
 x_558 = x_556;
}
lean_ctor_set(x_558, 0, x_557);
if (lean_is_scalar(x_551)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_551;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_550);
return x_559;
}
else
{
size_t x_560; size_t x_561; uint8_t x_562; 
x_560 = lean_ptr_addr(x_515);
lean_dec(x_515);
x_561 = lean_ptr_addr(x_540);
x_562 = lean_usize_dec_eq(x_560, x_561);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_516);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_563 = x_1;
} else {
 lean_dec_ref(x_1);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_564 = lean_alloc_ctor(0, 4, 0);
} else {
 x_564 = x_524;
}
lean_ctor_set(x_564, 0, x_514);
lean_ctor_set(x_564, 1, x_540);
lean_ctor_set(x_564, 2, x_533);
lean_ctor_set(x_564, 3, x_549);
if (lean_is_scalar(x_563)) {
 x_565 = lean_alloc_ctor(4, 1, 0);
} else {
 x_565 = x_563;
}
lean_ctor_set(x_565, 0, x_564);
if (lean_is_scalar(x_551)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_551;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_550);
return x_566;
}
else
{
uint8_t x_567; 
x_567 = lean_name_eq(x_516, x_533);
lean_dec(x_516);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_568 = x_1;
} else {
 lean_dec_ref(x_1);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_569 = lean_alloc_ctor(0, 4, 0);
} else {
 x_569 = x_524;
}
lean_ctor_set(x_569, 0, x_514);
lean_ctor_set(x_569, 1, x_540);
lean_ctor_set(x_569, 2, x_533);
lean_ctor_set(x_569, 3, x_549);
if (lean_is_scalar(x_568)) {
 x_570 = lean_alloc_ctor(4, 1, 0);
} else {
 x_570 = x_568;
}
lean_ctor_set(x_570, 0, x_569);
if (lean_is_scalar(x_551)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_551;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_550);
return x_571;
}
else
{
lean_object* x_572; 
lean_dec(x_549);
lean_dec(x_540);
lean_dec(x_533);
lean_dec(x_524);
lean_dec(x_514);
if (lean_is_scalar(x_551)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_551;
}
lean_ctor_set(x_572, 0, x_1);
lean_ctor_set(x_572, 1, x_550);
return x_572;
}
}
}
}
block_585:
{
lean_object* x_576; uint8_t x_577; 
lean_dec(x_575);
x_576 = lean_unsigned_to_nat(0u);
x_577 = lean_nat_dec_lt(x_576, x_574);
lean_dec(x_574);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_549);
x_578 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_579 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_578);
x_580 = l_Lean_Compiler_LCNF_AltCore_getCode(x_579);
lean_dec(x_579);
if (lean_is_scalar(x_547)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_547;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_550);
return x_581;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_array_fget(x_549, x_576);
lean_dec(x_549);
x_583 = l_Lean_Compiler_LCNF_AltCore_getCode(x_582);
lean_dec(x_582);
if (lean_is_scalar(x_547)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_547;
}
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_550);
return x_584;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_547);
lean_dec(x_540);
lean_dec(x_533);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_1);
x_597 = lean_ctor_get(x_548, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_548, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_599 = x_548;
} else {
 lean_dec_ref(x_548);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_540);
lean_dec(x_533);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_601 = lean_ctor_get(x_544, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_544, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_603 = x_544;
} else {
 lean_dec_ref(x_544);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_1);
x_605 = lean_ctor_get(x_523, 1);
lean_inc(x_605);
lean_dec(x_523);
x_606 = lean_ctor_get(x_525, 0);
lean_inc(x_606);
lean_dec(x_525);
x_607 = l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(x_606, x_522, x_2, x_3, x_4, x_360, x_6, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_524);
lean_dec(x_522);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_608 = lean_ctor_get(x_523, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_523, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_610 = x_523;
} else {
 lean_dec_ref(x_523);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_510);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_612 = lean_ctor_get(x_511, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_613 = x_511;
} else {
 lean_dec_ref(x_511);
 x_613 = lean_box(0);
}
x_614 = lean_ctor_get(x_512, 0);
lean_inc(x_614);
lean_dec(x_512);
if (lean_is_scalar(x_613)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_613;
}
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_612);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_510);
lean_dec(x_360);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_616 = lean_ctor_get(x_511, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_511, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_618 = x_511;
} else {
 lean_dec_ref(x_511);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_616);
lean_ctor_set(x_619, 1, x_617);
return x_619;
}
}
case 5:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_620 = lean_ctor_get(x_361, 1);
lean_inc(x_620);
lean_dec(x_361);
x_621 = lean_ctor_get(x_1, 0);
lean_inc(x_621);
x_622 = lean_st_ref_get(x_6, x_620);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
lean_dec(x_622);
x_624 = lean_st_ref_get(x_3, x_623);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = lean_ctor_get(x_625, 0);
lean_inc(x_627);
lean_dec(x_625);
lean_inc(x_621);
x_628 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_627, x_621);
lean_inc(x_628);
x_629 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_628, x_2, x_3, x_4, x_360, x_6, x_626);
lean_dec(x_6);
lean_dec(x_360);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_631 = x_629;
} else {
 lean_dec_ref(x_629);
 x_631 = lean_box(0);
}
x_632 = lean_name_eq(x_621, x_628);
lean_dec(x_621);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_633 = x_1;
} else {
 lean_dec_ref(x_1);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(5, 1, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_628);
if (lean_is_scalar(x_631)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_631;
}
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_630);
return x_635;
}
else
{
lean_object* x_636; 
lean_dec(x_628);
if (lean_is_scalar(x_631)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_631;
}
lean_ctor_set(x_636, 0, x_1);
lean_ctor_set(x_636, 1, x_630);
return x_636;
}
}
default: 
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; size_t x_647; size_t x_648; uint8_t x_649; 
lean_dec(x_360);
lean_dec(x_4);
lean_dec(x_2);
x_637 = lean_ctor_get(x_361, 1);
lean_inc(x_637);
lean_dec(x_361);
x_638 = lean_ctor_get(x_1, 0);
lean_inc(x_638);
x_639 = lean_st_ref_get(x_6, x_637);
lean_dec(x_6);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
lean_dec(x_639);
x_641 = lean_st_ref_get(x_3, x_640);
lean_dec(x_3);
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_644 = x_641;
} else {
 lean_dec_ref(x_641);
 x_644 = lean_box(0);
}
x_645 = lean_ctor_get(x_642, 0);
lean_inc(x_645);
lean_dec(x_642);
lean_inc(x_638);
x_646 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_645, x_638);
x_647 = lean_ptr_addr(x_638);
lean_dec(x_638);
x_648 = lean_ptr_addr(x_646);
x_649 = lean_usize_dec_eq(x_647, x_648);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_650 = x_1;
} else {
 lean_dec_ref(x_1);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(6, 1, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_646);
if (lean_is_scalar(x_644)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_644;
}
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_643);
return x_652;
}
else
{
lean_object* x_653; 
lean_dec(x_646);
if (lean_is_scalar(x_644)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_644;
}
lean_ctor_set(x_653, 0, x_1);
lean_ctor_set(x_653, 1, x_643);
return x_653;
}
}
}
}
}
else
{
lean_object* x_654; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_654 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_654;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_23; 
x_13 = lean_array_uget(x_1, x_3);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_4);
x_14 = x_30;
x_15 = x_10;
goto block_22;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_24, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_array_fget(x_26, x_27);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_27, x_36);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_37);
x_38 = l_Lean_Expr_isFVar(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_35, x_39, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_array_push(x_25, x_43);
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = l_Lean_Compiler_LCNF_Simp_addSubst(x_45, x_47, x_5, x_6, x_7, x_8, x_9, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_ctor_set(x_4, 1, x_44);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
x_14 = x_50;
x_15 = x_49;
goto block_22;
}
else
{
uint8_t x_51; 
lean_dec(x_24);
lean_free_object(x_4);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
lean_dec(x_13);
x_56 = l_Lean_Compiler_LCNF_Simp_addSubst(x_55, x_35, x_5, x_6, x_7, x_8, x_9, x_10);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_4);
x_14 = x_58;
x_15 = x_57;
goto block_22;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_24);
x_59 = lean_array_fget(x_26, x_27);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_27, x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_28);
x_63 = l_Lean_Expr_isFVar(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_59, x_64, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_array_push(x_25, x_68);
x_70 = lean_ctor_get(x_13, 0);
lean_inc(x_70);
lean_dec(x_13);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = l_Lean_Expr_fvar___override(x_71);
x_73 = l_Lean_Compiler_LCNF_Simp_addSubst(x_70, x_72, x_5, x_6, x_7, x_8, x_9, x_67);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_62);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_4);
x_14 = x_75;
x_15 = x_74;
goto block_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
lean_free_object(x_4);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
lean_dec(x_13);
x_81 = l_Lean_Compiler_LCNF_Simp_addSubst(x_80, x_59, x_5, x_6, x_7, x_8, x_9, x_10);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_ctor_set(x_4, 0, x_62);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_4);
x_14 = x_83;
x_15 = x_82;
goto block_22;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_4, 0);
x_85 = lean_ctor_get(x_4, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_4);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 2);
lean_inc(x_88);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_13);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_14 = x_91;
x_15 = x_10;
goto block_22;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
x_93 = lean_array_fget(x_86, x_87);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_87, x_94);
lean_dec(x_87);
if (lean_is_scalar(x_92)) {
 x_96 = lean_alloc_ctor(0, 3, 0);
} else {
 x_96 = x_92;
}
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_88);
x_97 = l_Lean_Expr_isFVar(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_99 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_93, x_98, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_array_push(x_85, x_102);
x_104 = lean_ctor_get(x_13, 0);
lean_inc(x_104);
lean_dec(x_13);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = l_Lean_Expr_fvar___override(x_105);
x_107 = l_Lean_Compiler_LCNF_Simp_addSubst(x_104, x_106, x_5, x_6, x_7, x_8, x_9, x_101);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_103);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_14 = x_110;
x_15 = x_108;
goto block_22;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_96);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_13, 0);
lean_inc(x_115);
lean_dec(x_13);
x_116 = l_Lean_Compiler_LCNF_Simp_addSubst(x_115, x_93, x_5, x_6, x_7, x_8, x_9, x_10);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_96);
lean_ctor_set(x_118, 1, x_85);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_14 = x_119;
x_15 = x_117;
goto block_22;
}
}
}
block_22:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_18;
x_10 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_14, x_8);
x_16 = l_Lean_Expr_fvar___override(x_15);
x_17 = l_Lean_Compiler_LCNF_Simp_findCtor(x_16, x_2, x_3, x_4, x_5, x_6, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_6, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = l_Lean_Expr_constructorApp_x3f(x_24, x_18, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
uint8_t x_28; 
lean_free_object(x_20);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Compiler_LCNF_eraseCode(x_37, x_4, x_5, x_6, x_23);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 2);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_array_get_size(x_31);
x_46 = l_Array_toSubarray___rarg(x_31, x_44, x_45);
x_47 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_get_size(x_42);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_42, x_50, x_51, x_48, x_2, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l_Lean_Compiler_LCNF_Simp_simp(x_43, x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Compiler_LCNF_eraseParams(x_42, x_4, x_5, x_6, x_58);
lean_dec(x_42);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_55, x_57, x_2, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_55);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_ctor_set(x_26, 0, x_63);
lean_ctor_set(x_61, 0, x_26);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_61);
lean_ctor_set(x_26, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_26);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_55);
lean_dec(x_42);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_56);
if (x_67 == 0)
{
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_56, 0);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_56);
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
lean_dec(x_42);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_52);
if (x_71 == 0)
{
return x_52;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_52, 0);
x_73 = lean_ctor_get(x_52, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_52);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_31);
lean_dec(x_30);
x_75 = lean_ctor_get(x_40, 1);
lean_inc(x_75);
lean_dec(x_40);
x_76 = lean_ctor_get(x_35, 0);
lean_inc(x_76);
lean_dec(x_35);
x_77 = l_Lean_Compiler_LCNF_Simp_simp(x_76, x_2, x_3, x_4, x_5, x_6, x_75);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set(x_26, 0, x_79);
lean_ctor_set(x_77, 0, x_26);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
lean_ctor_set(x_26, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_26);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_26);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = lean_ctor_get(x_26, 0);
lean_inc(x_87);
lean_dec(x_26);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_Compiler_LCNF_eraseCode(x_95, x_4, x_5, x_6, x_23);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; lean_object* x_110; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 2);
lean_inc(x_101);
lean_dec(x_93);
x_102 = lean_ctor_get(x_88, 3);
lean_inc(x_102);
lean_dec(x_88);
x_103 = lean_array_get_size(x_89);
x_104 = l_Array_toSubarray___rarg(x_89, x_102, x_103);
x_105 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_get_size(x_100);
x_108 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_109 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_100, x_108, x_109, x_106, x_2, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_114 = l_Lean_Compiler_LCNF_Simp_simp(x_101, x_2, x_3, x_4, x_5, x_6, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Compiler_LCNF_eraseParams(x_100, x_4, x_5, x_6, x_116);
lean_dec(x_100);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_113, x_115, x_2, x_3, x_4, x_5, x_6, x_118);
lean_dec(x_113);
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
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_120);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_113);
lean_dec(x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = lean_ctor_get(x_110, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_110, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_131 = x_110;
} else {
 lean_dec_ref(x_110);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_89);
lean_dec(x_88);
x_133 = lean_ctor_get(x_98, 1);
lean_inc(x_133);
lean_dec(x_98);
x_134 = lean_ctor_get(x_93, 0);
lean_inc(x_134);
lean_dec(x_93);
x_135 = l_Lean_Compiler_LCNF_Simp_simp(x_134, x_2, x_3, x_4, x_5, x_6, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
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
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_136);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_20, 0);
x_146 = lean_ctor_get(x_20, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_20);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
x_148 = 1;
x_149 = l_Lean_Expr_constructorApp_x3f(x_147, x_18, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Compiler_LCNF_eraseCode(x_161, x_4, x_5, x_6, x_146);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_159, 2);
lean_inc(x_167);
lean_dec(x_159);
x_168 = lean_ctor_get(x_154, 3);
lean_inc(x_168);
lean_dec(x_154);
x_169 = lean_array_get_size(x_155);
x_170 = l_Array_toSubarray___rarg(x_155, x_168, x_169);
x_171 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_get_size(x_166);
x_174 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_175 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_166, x_174, x_175, x_172, x_2, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_180 = l_Lean_Compiler_LCNF_Simp_simp(x_167, x_2, x_3, x_4, x_5, x_6, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Compiler_LCNF_eraseParams(x_166, x_4, x_5, x_6, x_182);
lean_dec(x_166);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_179, x_181, x_2, x_3, x_4, x_5, x_6, x_184);
lean_dec(x_179);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_153;
}
lean_ctor_set(x_189, 0, x_186);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_179);
lean_dec(x_166);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_180, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_153);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = lean_ctor_get(x_176, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_176, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_197 = x_176;
} else {
 lean_dec_ref(x_176);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_155);
lean_dec(x_154);
x_199 = lean_ctor_get(x_164, 1);
lean_inc(x_199);
lean_dec(x_164);
x_200 = lean_ctor_get(x_159, 0);
lean_inc(x_200);
lean_dec(x_159);
x_201 = l_Lean_Compiler_LCNF_Simp_simp(x_200, x_2, x_3, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_153;
}
lean_ctor_set(x_205, 0, x_202);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_153);
x_207 = lean_ctor_get(x_201, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_simp___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_simp___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*6);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_4);
lean_ctor_set(x_26, 4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_15, 0, x_27);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_4);
lean_ctor_set(x_29, 4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", size: ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # visited: ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # inline: ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # inline local: ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_8);
x_15 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1;
lean_inc(x_1);
x_16 = l_Lean_Name_str___override(x_1, x_15);
lean_inc(x_16);
x_103 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_16, x_9, x_10, x_11, x_12, x_13, x_14);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_7);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_17 = x_106;
goto block_102;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_108 = l_Lean_Compiler_LCNF_ppDecl(x_7, x_11, x_12, x_13, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_109);
lean_inc(x_16);
x_112 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_16, x_111, x_9, x_10, x_11, x_12, x_13, x_110);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_17 = x_113;
goto block_102;
}
else
{
uint8_t x_114; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_108);
if (x_114 == 0)
{
return x_108;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_108, 0);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_108);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_102:
{
lean_object* x_18; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2;
x_22 = l_Lean_Name_str___override(x_16, x_21);
lean_inc(x_22);
x_76 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_22, x_9, x_10, x_11, x_12, x_13, x_20);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_22);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_23 = x_79;
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_19);
x_81 = l_Lean_Compiler_LCNF_ppCode(x_19, x_11, x_12, x_13, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_3);
x_84 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_84, 0, x_3);
x_85 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_82);
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
x_92 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_22, x_91, x_9, x_10, x_11, x_12, x_13, x_83);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_23 = x_93;
goto block_75;
}
else
{
uint8_t x_94; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_81);
if (x_94 == 0)
{
return x_81;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_81, 0);
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_81);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_75:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_st_ref_get(x_13, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3;
x_30 = l_Lean_Name_str___override(x_1, x_29);
lean_inc(x_30);
x_31 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_30, x_9, x_10, x_11, x_12, x_13, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_27);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_3, x_4, x_5, x_6, x_19, x_35, x_9, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
lean_inc(x_3);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_3);
x_39 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
x_44 = l_Lean_Compiler_LCNF_Code_size_go(x_19, x_43);
x_45 = l_Nat_repr(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_ctor_get(x_27, 3);
lean_inc(x_51);
x_52 = l_Nat_repr(x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_ctor_get(x_27, 4);
lean_inc(x_58);
x_59 = l_Nat_repr(x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_27, 5);
lean_inc(x_65);
lean_dec(x_27);
x_66 = l_Nat_repr(x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_39);
x_71 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_30, x_70, x_9, x_10, x_11, x_12, x_13, x_37);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_3, x_4, x_5, x_6, x_19, x_72, x_9, x_10, x_11, x_12, x_13, x_73);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_72);
return x_74;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_18);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_18, 0);
x_100 = lean_ctor_get(x_18, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_18);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2(x_21, x_12, x_8, x_9, x_10, x_11, x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_st_ref_get(x_6, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_30, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_8);
x_35 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_16, x_43, x_2, x_3, x_4, x_5, x_6, x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_48 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2(x_47, x_12, x_8, x_9, x_10, x_11, x_1, x_45, x_2, x_3, x_4, x_5, x_6, x_46);
return x_48;
}
else
{
uint8_t x_49; 
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
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
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
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1;
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*6, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_9, x_14, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_5, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_1 = x_27;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_isTemplateLike(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_2, sizeof(void*)*1 + 1, x_14);
x_15 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_16);
lean_dec(x_2);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_17);
x_20 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_19, x_3, x_4, x_5, x_12);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Decl_simp(x_2, x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lambda__1), 6, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_simp___closed__1;
x_5 = 0;
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_3, x_5, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_7 = 0;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1;
x_11 = l_Lean_registerTraceClass(x_10, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2;
x_14 = l_Lean_registerTraceClass(x_13, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3;
x_17 = l_Lean_registerTraceClass(x_16, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InlineAttrs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Specialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Stage1(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InlineAttrs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Stage1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___closed__1);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__1);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__2);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__4);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__6);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__7);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__8);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__9);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__10);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__11);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__15);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__16);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__17);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__18);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__20);
l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__1);
l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo = _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo);
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo();
l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default = _init_l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default);
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1);
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__3);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__5);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6);
l_Lean_Compiler_LCNF_Simp_Config_smallThreshold___default = _init_l_Lean_Compiler_LCNF_Simp_Config_smallThreshold___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Config_smallThreshold___default);
l_Lean_Compiler_LCNF_Simp_Config_etaPoly___default = _init_l_Lean_Compiler_LCNF_Simp_Config_etaPoly___default();
l_Lean_Compiler_LCNF_Simp_Config_inlinePartial___default = _init_l_Lean_Compiler_LCNF_Simp_Config_inlinePartial___default();
l_Lean_Compiler_LCNF_Simp_Config_implementedBy___default = _init_l_Lean_Compiler_LCNF_Simp_Config_implementedBy___default();
l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig___closed__1);
l_Lean_Compiler_LCNF_Simp_instInhabitedConfig = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedConfig);
l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1);
l_Lean_Compiler_LCNF_Simp_Context_config___default = _init_l_Lean_Compiler_LCNF_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_config___default);
l_Lean_Compiler_LCNF_Simp_Context_discrCtorMap___default = _init_l_Lean_Compiler_LCNF_Simp_Context_discrCtorMap___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_discrCtorMap___default);
l_Lean_Compiler_LCNF_Simp_State_subst___default = _init_l_Lean_Compiler_LCNF_Simp_State_subst___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_subst___default);
l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1);
l_Lean_Compiler_LCNF_Simp_State_used___default = _init_l_Lean_Compiler_LCNF_Simp_State_used___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_used___default);
l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default = _init_l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default);
l_Lean_Compiler_LCNF_Simp_State_simplified___default = _init_l_Lean_Compiler_LCNF_Simp_State_simplified___default();
l_Lean_Compiler_LCNF_Simp_State_visited___default = _init_l_Lean_Compiler_LCNF_Simp_State_visited___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_visited___default);
l_Lean_Compiler_LCNF_Simp_State_inline___default = _init_l_Lean_Compiler_LCNF_Simp_State_inline___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_inline___default);
l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default = _init_l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default);
l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1);
l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__2);
l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM = _init_l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__3);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__4);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__5);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__6);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__3);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___closed__4);
l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1 = _init_l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__1);
l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2 = _init_l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8);
l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1);
l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2);
l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__3);
l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__4);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__6);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5);
l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2);
l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1 = _init_l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__1);
l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2 = _init_l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__2___closed__2);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1);
l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1);
l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1 = _init_l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1);
l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1 = _init_l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8___closed__2);
l_Lean_Compiler_LCNF_Simp_simp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__1);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__6);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__9);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__10);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__11);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12);
l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__13);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__1);
l_Lean_Compiler_LCNF_simp___closed__1 = _init_l_Lean_Compiler_LCNF_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_simp___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945____closed__3);
res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11945_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
