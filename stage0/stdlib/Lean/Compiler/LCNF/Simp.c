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
uint8_t l_Std_HashSetImp_contains___at_Lean_MVarId_getNondepPropHyps___spec__16(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_subst___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_map___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__13;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_eraseCodeDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1681_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9;
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
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__3;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedConfig;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_HashSetImp_insert___at_Lean_MVarId_getNondepPropHyps___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_getMaxOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_isPure(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*);
uint8_t lean_has_specialize_attribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f___spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__8;
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Compiler_LCNF_Simp_findCtor___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__5;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_eraseFVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__8(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getStage1Decl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_State_simplified___default;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173____closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstructorApp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_Config_inlinePartial___default;
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_HashMapImp_erase___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1;
lean_object* l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isJpCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
static lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFVarsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10;
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
x_12 = l_Lean_Compiler_LCNF_getLocalDecl(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_LocalDecl_userName(x_13);
lean_dec(x_13);
x_18 = 1;
x_19 = l_Lean_Name_toString(x_17, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__4;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___spec__4___closed__6;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_reprFunDeclInfo____x40_Lean_Compiler_LCNF_Simp___hyg_173_(x_26, x_25);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
x_1 = x_9;
x_2 = x_30;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_getLocalDecl(x_6, x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_11);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_dec(x_11);
x_1 = x_19;
x_5 = x_18;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
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
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_7, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_32 = x_8;
} else {
 lean_dec_ref(x_8);
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
case 10:
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_1 = x_35;
goto _start;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
return x_38;
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Compiler_LCNF_getLocalDecl(x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_9);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 1;
x_1 = x_15;
x_2 = x_16;
x_6 = x_14;
goto _start;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 10:
{
if (x_2 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = 1;
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
default: 
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_6);
return x_26;
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
x_29 = lean_ctor_get(x_5, 1);
x_30 = l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(x_29, x_1, x_26);
lean_ctor_set(x_5, 1, x_30);
x_31 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = l_Std_RBNode_insert___at_Lean_Compiler_LCNF_Simp_withDiscrCtor___spec__7(x_33, x_1, x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_6(x_4, x_35, x_6, x_7, x_8, x_9, x_27);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
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
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(x_29, x_1, x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_35, x_3, x_4, x_5, x_6, x_7, x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___lambda__2(x_33, x_1, x_34, x_37, x_3, x_4, x_5, x_6, x_7, x_38);
return x_39;
}
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_40, 4);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_2 = x_41;
x_8 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 3:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = l_Lean_Compiler_LCNF_getFunDecl(x_50, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_Simp_addFunOcc(x_54, x_3, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 4:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_array_get_size(x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_lt(x_63, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_62, x_62);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
return x_69;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go___spec__1(x_1, x_61, x_70, x_71, x_72, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_61);
return x_73;
}
}
}
default: 
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_8);
return x_75;
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
x_9 = lean_ctor_get(x_2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 5);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_19);
x_26 = lean_st_ref_set(x_4, x_25, x_15);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 4);
x_31 = 1;
lean_inc(x_30);
lean_inc(x_29);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 4);
x_37 = 1;
lean_inc(x_36);
lean_inc(x_35);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
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
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_1);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_1, x_2);
x_11 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_1, x_2);
x_12 = l_Lean_Compiler_LCNF_Simp_incInline___rarg(x_5, x_6, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
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
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = l_Lean_Compiler_LCNF_Decl_getArity(x_24);
x_26 = lean_nat_dec_lt(x_3, x_25);
lean_dec(x_25);
lean_dec(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_11);
x_27 = lean_box(0);
x_28 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_24, x_2, x_27, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_29 = lean_box(0);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l_Lean_Compiler_LCNF_Decl_getArity(x_31);
x_33 = lean_nat_dec_lt(x_3, x_32);
lean_dec(x_32);
lean_dec(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_31, x_2, x_34, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_box(0);
x_41 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_39, x_2, x_40, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_11 = 1;
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_Simp_findExpr(x_10, x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_6, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
lean_inc(x_15);
x_23 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_21, x_22, x_15);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(x_15, x_16, x_9, x_25, x_2, x_3, x_4, x_5, x_6, x_20);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 0;
lean_inc(x_15);
x_31 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_29, x_30, x_15);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__4(x_15, x_16, x_9, x_34, x_2, x_3, x_4, x_5, x_6, x_28);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = l_Lean_Compiler_LCNF_Simp_findFunDecl_x3f(x_10, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_37, 1);
x_47 = lean_ctor_get(x_37, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
lean_ctor_set(x_37, 0, x_50);
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_37);
x_51 = lean_box(0);
x_52 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_48, x_51, x_2, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_54, x_58, x_2, x_3, x_4, x_5, x_6, x_53);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_37);
if (x_60 == 0)
{
return x_37;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_37, 0);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_37);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_12);
if (x_64 == 0)
{
return x_12;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
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
x_21 = l_Lean_Compiler_LCNF_mkAuxParam(x_19, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = lean_array_push(x_15, x_22);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_Expr_fvar___override(x_26);
x_28 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__3(x_16, x_25, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_4 = x_29;
x_10 = x_23;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_11 = l_Array_toSubarray___rarg(x_2, x_10, x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
x_17 = 0;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_12, x_16, x_17, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_29 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_23, x_26, x_28, x_19, x_3, x_4, x_5, x_6, x_7, x_20);
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
x_35 = l_Lean_Compiler_LCNF_Code_internalize(x_34, x_33, x_5, x_6, x_7, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_39 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_38, x_36, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_42 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_32, x_36, x_41, x_5, x_6, x_7, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_55 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_48, x_52, x_54, x_50, x_3, x_4, x_5, x_6, x_7, x_20);
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
x_61 = l_Lean_Compiler_LCNF_Code_internalize(x_60, x_59, x_5, x_6, x_7, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_62);
x_65 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_go(x_64, x_62, x_3, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_58, x_62, x_67, x_5, x_6, x_7, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_2);
x_16 = lean_nat_dec_lt(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_4);
x_20 = l_Array_toSubarray___rarg(x_4, x_19, x_15);
x_21 = l_Array_ofSubarray___rarg(x_20);
x_22 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_21);
x_23 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_17, x_18, x_21, x_22, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_75; uint8_t x_90; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_90 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_6, x_14);
if (x_90 == 0)
{
uint8_t x_91; 
lean_free_object(x_23);
x_91 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_25);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_27 = x_92;
goto block_74;
}
else
{
lean_object* x_93; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_93 = lean_box(0);
x_75 = x_93;
goto block_89;
}
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_eq(x_3, x_15);
if (x_94 == 0)
{
uint8_t x_95; 
lean_free_object(x_23);
x_95 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_25);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_27 = x_96;
goto block_74;
}
else
{
lean_object* x_97; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_97 = lean_box(0);
x_75 = x_97;
goto block_89;
}
}
else
{
lean_object* x_98; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_25);
lean_ctor_set(x_23, 0, x_98);
return x_23;
}
}
block_74:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
x_28 = l_Lean_Expr_getAppFn(x_5);
lean_dec(x_5);
x_29 = l_Lean_mkAppN(x_28, x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Compiler_LCNF_inferType(x_29, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Compiler_LCNF_mkAuxParam(x_31, x_10, x_11, x_12, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_nat_dec_lt(x_15, x_3);
lean_dec(x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_4);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_38 = l_Lean_Compiler_LCNF_replaceFVar(x_6, x_14, x_37, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_34, x_25, x_39, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_9);
lean_dec(x_8);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
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
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = lean_array_get_size(x_4);
x_49 = l_Array_toSubarray___rarg(x_4, x_15, x_48);
x_50 = l_Array_ofSubarray___rarg(x_49);
x_51 = l_Lean_mkAppN(x_47, x_50);
x_52 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_53 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_51, x_52, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = l_Lean_Compiler_LCNF_replaceFVar(x_6, x_14, x_56, x_10, x_11, x_12, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_34, x_25, x_60, x_8, x_9, x_10, x_11, x_12, x_59);
lean_dec(x_9);
lean_dec(x_8);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_54);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
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
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_30);
if (x_70 == 0)
{
return x_30;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_30, 0);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_30);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
block_89:
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_75);
x_76 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 10, 5);
lean_closure_set(x_76, 0, x_15);
lean_closure_set(x_76, 1, x_3);
lean_closure_set(x_76, 2, x_6);
lean_closure_set(x_76, 3, x_14);
lean_closure_set(x_76, 4, x_4);
x_77 = l_Lean_Compiler_LCNF_Code_bind(x_25, x_76, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
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
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_149; uint8_t x_162; 
x_99 = lean_ctor_get(x_23, 0);
x_100 = lean_ctor_get(x_23, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_23);
x_162 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_6, x_14);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_99);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_box(0);
x_101 = x_164;
goto block_148;
}
else
{
lean_object* x_165; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_165 = lean_box(0);
x_149 = x_165;
goto block_161;
}
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_eq(x_3, x_15);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_99);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_box(0);
x_101 = x_168;
goto block_148;
}
else
{
lean_object* x_169; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_169 = lean_box(0);
x_149 = x_169;
goto block_161;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_99);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_100);
return x_171;
}
}
block_148:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_101);
x_102 = l_Lean_Expr_getAppFn(x_5);
lean_dec(x_5);
x_103 = l_Lean_mkAppN(x_102, x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_104 = l_Lean_Compiler_LCNF_inferType(x_103, x_10, x_11, x_12, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Compiler_LCNF_mkAuxParam(x_105, x_10, x_11, x_12, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_nat_dec_lt(x_15, x_3);
lean_dec(x_3);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_15);
lean_dec(x_4);
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_112 = l_Lean_Compiler_LCNF_replaceFVar(x_6, x_14, x_111, x_10, x_11, x_12, x_109);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_108, x_99, x_113, x_8, x_9, x_10, x_11, x_12, x_114);
lean_dec(x_9);
lean_dec(x_8);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_108, 0);
lean_inc(x_120);
x_121 = l_Lean_Expr_fvar___override(x_120);
x_122 = lean_array_get_size(x_4);
x_123 = l_Array_toSubarray___rarg(x_4, x_15, x_122);
x_124 = l_Array_ofSubarray___rarg(x_123);
x_125 = l_Lean_mkAppN(x_121, x_124);
x_126 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_127 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_125, x_126, x_10, x_11, x_12, x_109);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_131 = l_Lean_Compiler_LCNF_replaceFVar(x_6, x_14, x_130, x_10, x_11, x_12, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_108, x_99, x_134, x_8, x_9, x_10, x_11, x_12, x_133);
lean_dec(x_9);
lean_dec(x_8);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_128);
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_138 = x_131;
} else {
 lean_dec_ref(x_131);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_127, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_142 = x_127;
} else {
 lean_dec_ref(x_127);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_99);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_104, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_104, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_146 = x_104;
} else {
 lean_dec_ref(x_104);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
block_161:
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_149);
x_150 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__3___boxed), 10, 5);
lean_closure_set(x_150, 0, x_15);
lean_closure_set(x_150, 1, x_3);
lean_closure_set(x_150, 2, x_6);
lean_closure_set(x_150, 3, x_14);
lean_closure_set(x_150, 4, x_4);
x_151 = l_Lean_Compiler_LCNF_Code_bind(x_99, x_150, x_10, x_11, x_12, x_100);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
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
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_151, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_159 = x_151;
} else {
 lean_dec_ref(x_151);
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
}
}
else
{
uint8_t x_172; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = !lean_is_exclusive(x_23);
if (x_172 == 0)
{
return x_23;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_23, 0);
x_174 = lean_ctor_get(x_23, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_23);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_176 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_2, x_4, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = l_Lean_Expr_fvar___override(x_179);
x_181 = l_Lean_Compiler_LCNF_Simp_addSubst(x_14, x_180, x_8, x_9, x_10, x_11, x_12, x_178);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_181, 0);
lean_dec(x_183);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_6);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_181, 0, x_185);
return x_181;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_177);
lean_ctor_set(x_187, 1, x_6);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
return x_176;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_176, 0);
x_192 = lean_ctor_get(x_176, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_176);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__3;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inlining ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10() {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
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
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_23);
x_25 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
lean_inc(x_10);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_10, x_26, x_28);
x_30 = lean_array_get_size(x_29);
x_31 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
x_32 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__1(x_31, x_4, x_5, x_6, x_7, x_8, x_22);
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
x_36 = lean_box(0);
x_37 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_1, x_20, x_30, x_29, x_10, x_2, x_36, x_4, x_5, x_6, x_7, x_8, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_10);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_10);
x_40 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_inlineApp_x3f___spec__2(x_31, x_43, x_4, x_5, x_6, x_7, x_8, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__4(x_1, x_20, x_30, x_29, x_10, x_2, x_45, x_4, x_5, x_6, x_7, x_8, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
x_15 = l_Std_HashSetImp_insert___at_Lean_MVarId_getNondepPropHyps___spec__2(x_14, x_1);
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
x_30 = l_Std_HashSetImp_insert___at_Lean_MVarId_getNondepPropHyps___spec__2(x_24, x_1);
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
x_14 = l_Std_HashSetImp_contains___at_Lean_MVarId_getNondepPropHyps___spec__16(x_13, x_1);
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
x_19 = l_Std_HashSetImp_contains___at_Lean_MVarId_getNondepPropHyps___spec__16(x_18, x_1);
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
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_57; uint8_t x_58; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_57 = lean_array_get_size(x_1);
x_58 = lean_nat_dec_lt(x_14, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_60 = l_panic___at_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___spec__1(x_59);
x_15 = x_60;
goto block_56;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget(x_1, x_14);
x_15 = x_61;
goto block_56;
}
block_56:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_15);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_CodeDecl_isPure(x_15);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_21);
x_22 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_21, x_4, x_5, x_6, x_7, x_8, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_3);
x_2 = x_14;
x_3 = x_24;
x_9 = x_23;
goto _start;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_26);
x_27 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_26, x_4, x_5, x_6, x_7, x_8, x_19);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_14;
x_3 = x_29;
x_9 = x_28;
goto _start;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_31, x_4, x_5, x_6, x_7, x_8, x_19);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_14;
x_3 = x_34;
x_9 = x_33;
goto _start;
}
}
}
else
{
uint8_t x_36; 
x_36 = lean_unbox(x_18);
lean_dec(x_18);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_15);
x_37 = 1;
x_38 = l_Lean_Compiler_LCNF_eraseFVar(x_16, x_37, x_6, x_7, x_8, x_19);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_2 = x_14;
x_9 = x_39;
goto _start;
}
else
{
lean_dec(x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_41);
lean_dec(x_15);
lean_inc(x_41);
x_42 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_41, x_4, x_5, x_6, x_7, x_8, x_19);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_3);
x_2 = x_14;
x_3 = x_44;
x_9 = x_43;
goto _start;
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_46);
x_47 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_46, x_4, x_5, x_6, x_7, x_8, x_19);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_3);
x_2 = x_14;
x_3 = x_49;
x_9 = x_48;
goto _start;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_51);
x_52 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_51, x_4, x_5, x_6, x_7, x_8, x_19);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_3);
x_2 = x_14;
x_3 = x_54;
x_9 = x_53;
goto _start;
}
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = 1;
x_15 = l_Lean_Compiler_LCNF_eraseFVar(x_13, x_14, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_10);
return x_21;
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
x_3 = lean_unsigned_to_nat(595u);
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
x_3 = lean_unsigned_to_nat(598u);
x_4 = lean_unsigned_to_nat(32u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Compiler_LCNF_Simp_findExpr(x_1, x_10, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
lean_inc(x_12);
x_19 = l_Lean_Expr_constructorApp_x3f(x_18, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_21, x_7, x_8, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Compiler_LCNF_Decl_getArity(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_36);
x_38 = lean_nat_dec_eq(x_35, x_37);
lean_dec(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_23);
lean_inc(x_34);
x_40 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_34, x_22);
x_41 = lean_ctor_get(x_34, 3);
lean_inc(x_41);
lean_dec(x_34);
x_42 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_37);
x_43 = lean_mk_array(x_37, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_37, x_44);
lean_dec(x_37);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_43, x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_41, x_40, x_46, x_10, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_dec(x_23);
x_56 = lean_ctor_get(x_24, 0);
lean_inc(x_56);
lean_dec(x_24);
x_57 = l_Lean_Compiler_LCNF_Decl_getArity(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_58);
x_60 = lean_nat_dec_eq(x_57, x_59);
lean_dec(x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_56);
x_63 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_56, x_22);
x_64 = lean_ctor_get(x_56, 3);
lean_inc(x_64);
lean_dec(x_56);
x_65 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_59);
x_66 = lean_mk_array(x_59, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_59, x_67);
lean_dec(x_59);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_66, x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_64, x_63, x_69, x_10, x_4, x_5, x_6, x_7, x_8, x_55);
lean_dec(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
uint8_t x_78; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_23);
if (x_78 == 0)
{
return x_23;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_23, 0);
x_80 = lean_ctor_get(x_23, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_23);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_17;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_16);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
x_84 = lean_ctor_get(x_19, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_85 = x_19;
} else {
 lean_dec_ref(x_19);
 x_85 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_17);
x_86 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_87 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
lean_dec(x_2);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_nat_add(x_92, x_90);
lean_dec(x_90);
lean_dec(x_92);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_lt(x_93, x_94);
lean_dec(x_94);
x_96 = l_List_isEmpty___rarg(x_91);
if (x_95 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
lean_dec(x_89);
x_105 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_106 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_105);
x_97 = x_106;
goto block_104;
}
else
{
lean_object* x_107; 
x_107 = lean_array_fget(x_89, x_93);
lean_dec(x_93);
lean_dec(x_89);
x_97 = x_107;
goto block_104;
}
block_104:
{
if (x_96 == 0)
{
lean_dec(x_85);
lean_dec(x_17);
x_1 = x_97;
x_2 = x_91;
x_9 = x_16;
goto _start;
}
else
{
lean_dec(x_91);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
if (lean_is_scalar(x_85)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_85;
}
lean_ctor_set(x_100, 0, x_99);
if (lean_is_scalar(x_17)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_17;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_16);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_97);
lean_dec(x_85);
lean_dec(x_17);
x_102 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_103 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_103;
}
}
}
}
}
}
case 1:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_11, 1);
lean_inc(x_108);
lean_dec(x_11);
x_109 = lean_st_ref_get(x_8, x_108);
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
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec(x_110);
lean_inc(x_12);
x_114 = l_Lean_Expr_constructorApp_x3f(x_113, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_115) == 4)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_112);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_8);
lean_inc(x_7);
x_118 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_116, x_7, x_8, x_111);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_dec(x_117);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 0);
lean_dec(x_121);
x_122 = lean_box(0);
lean_ctor_set(x_118, 0, x_122);
return x_118;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_127 = lean_ctor_get(x_118, 1);
x_128 = lean_ctor_get(x_118, 0);
lean_dec(x_128);
x_129 = lean_ctor_get(x_119, 0);
lean_inc(x_129);
lean_dec(x_119);
x_130 = l_Lean_Compiler_LCNF_Decl_getArity(x_129);
x_131 = lean_unsigned_to_nat(0u);
x_132 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_131);
x_133 = lean_nat_dec_eq(x_130, x_132);
lean_dec(x_130);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_117);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_box(0);
lean_ctor_set(x_118, 0, x_134);
return x_118;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_free_object(x_118);
lean_inc(x_129);
x_135 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_129, x_117);
x_136 = lean_ctor_get(x_129, 3);
lean_inc(x_136);
lean_dec(x_129);
x_137 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_132);
x_138 = lean_mk_array(x_132, x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_sub(x_132, x_139);
lean_dec(x_132);
x_141 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_138, x_140);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_142 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_136, x_135, x_141, x_10, x_4, x_5, x_6, x_7, x_8, x_127);
lean_dec(x_136);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
return x_145;
}
else
{
uint8_t x_146; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_142);
if (x_146 == 0)
{
return x_142;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_142, 0);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_142);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_118, 1);
lean_inc(x_150);
lean_dec(x_118);
x_151 = lean_ctor_get(x_119, 0);
lean_inc(x_151);
lean_dec(x_119);
x_152 = l_Lean_Compiler_LCNF_Decl_getArity(x_151);
x_153 = lean_unsigned_to_nat(0u);
x_154 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_153);
x_155 = lean_nat_dec_eq(x_152, x_154);
lean_dec(x_152);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_154);
lean_dec(x_151);
lean_dec(x_117);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_inc(x_151);
x_158 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_151, x_117);
x_159 = lean_ctor_get(x_151, 3);
lean_inc(x_159);
lean_dec(x_151);
x_160 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_154);
x_161 = lean_mk_array(x_154, x_160);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_sub(x_154, x_162);
lean_dec(x_154);
x_164 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_161, x_163);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_165 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_159, x_158, x_164, x_10, x_4, x_5, x_6, x_7, x_8, x_150);
lean_dec(x_159);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_117);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_118);
if (x_173 == 0)
{
return x_118;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_118, 0);
x_175 = lean_ctor_get(x_118, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_118);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_115);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_177 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_112;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_111);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_12);
x_179 = lean_ctor_get(x_114, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_180 = x_114;
} else {
 lean_dec_ref(x_114);
 x_180 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_112);
x_181 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_182 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_181, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; 
x_183 = lean_ctor_get(x_179, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_dec(x_179);
x_185 = lean_ctor_get(x_2, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 1);
lean_inc(x_186);
lean_dec(x_2);
x_187 = lean_ctor_get(x_183, 3);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_nat_add(x_187, x_185);
lean_dec(x_185);
lean_dec(x_187);
x_189 = lean_array_get_size(x_184);
x_190 = lean_nat_dec_lt(x_188, x_189);
lean_dec(x_189);
x_191 = l_List_isEmpty___rarg(x_186);
if (x_190 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_188);
lean_dec(x_184);
x_200 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_201 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_200);
x_192 = x_201;
goto block_199;
}
else
{
lean_object* x_202; 
x_202 = lean_array_fget(x_184, x_188);
lean_dec(x_188);
lean_dec(x_184);
x_192 = x_202;
goto block_199;
}
block_199:
{
if (x_191 == 0)
{
lean_dec(x_180);
lean_dec(x_112);
x_1 = x_192;
x_2 = x_186;
x_9 = x_111;
goto _start;
}
else
{
lean_dec(x_186);
if (lean_obj_tag(x_192) == 1)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
if (lean_is_scalar(x_180)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_180;
}
lean_ctor_set(x_195, 0, x_194);
if (lean_is_scalar(x_112)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_112;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_111);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_192);
lean_dec(x_180);
lean_dec(x_112);
x_197 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_198 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_197, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
return x_198;
}
}
}
}
}
}
case 2:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_11, 1);
lean_inc(x_203);
lean_dec(x_11);
x_204 = lean_st_ref_get(x_8, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
lean_dec(x_205);
lean_inc(x_12);
x_209 = l_Lean_Expr_constructorApp_x3f(x_208, x_12);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_210) == 4)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_207);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_8);
lean_inc(x_7);
x_213 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_211, x_7, x_8, x_206);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = !lean_is_exclusive(x_213);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_213, 0);
lean_dec(x_216);
x_217 = lean_box(0);
lean_ctor_set(x_213, 0, x_217);
return x_213;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
lean_dec(x_213);
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_213);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_222 = lean_ctor_get(x_213, 1);
x_223 = lean_ctor_get(x_213, 0);
lean_dec(x_223);
x_224 = lean_ctor_get(x_214, 0);
lean_inc(x_224);
lean_dec(x_214);
x_225 = l_Lean_Compiler_LCNF_Decl_getArity(x_224);
x_226 = lean_unsigned_to_nat(0u);
x_227 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_226);
x_228 = lean_nat_dec_eq(x_225, x_227);
lean_dec(x_225);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_227);
lean_dec(x_224);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_box(0);
lean_ctor_set(x_213, 0, x_229);
return x_213;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_free_object(x_213);
lean_inc(x_224);
x_230 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_224, x_212);
x_231 = lean_ctor_get(x_224, 3);
lean_inc(x_231);
lean_dec(x_224);
x_232 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_227);
x_233 = lean_mk_array(x_227, x_232);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_nat_sub(x_227, x_234);
lean_dec(x_227);
x_236 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_233, x_235);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_237 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_231, x_230, x_236, x_10, x_4, x_5, x_6, x_7, x_8, x_222);
lean_dec(x_231);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_238, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_239);
return x_240;
}
else
{
uint8_t x_241; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_241 = !lean_is_exclusive(x_237);
if (x_241 == 0)
{
return x_237;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_237, 0);
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_237);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_245 = lean_ctor_get(x_213, 1);
lean_inc(x_245);
lean_dec(x_213);
x_246 = lean_ctor_get(x_214, 0);
lean_inc(x_246);
lean_dec(x_214);
x_247 = l_Lean_Compiler_LCNF_Decl_getArity(x_246);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_248);
x_250 = lean_nat_dec_eq(x_247, x_249);
lean_dec(x_247);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_inc(x_246);
x_253 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_246, x_212);
x_254 = lean_ctor_get(x_246, 3);
lean_inc(x_254);
lean_dec(x_246);
x_255 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_249);
x_256 = lean_mk_array(x_249, x_255);
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_nat_sub(x_249, x_257);
lean_dec(x_249);
x_259 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_256, x_258);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_260 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_254, x_253, x_259, x_10, x_4, x_5, x_6, x_7, x_8, x_245);
lean_dec(x_254);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_262);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_264 = lean_ctor_get(x_260, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_266 = x_260;
} else {
 lean_dec_ref(x_260);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = !lean_is_exclusive(x_213);
if (x_268 == 0)
{
return x_213;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_213, 0);
x_270 = lean_ctor_get(x_213, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_213);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_210);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_207;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_206);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_12);
x_274 = lean_ctor_get(x_209, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_275 = x_209;
} else {
 lean_dec_ref(x_209);
 x_275 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_207);
x_276 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_277 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_276, x_3, x_4, x_5, x_6, x_7, x_8, x_206);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_286; lean_object* x_287; 
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
lean_dec(x_274);
x_280 = lean_ctor_get(x_2, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_2, 1);
lean_inc(x_281);
lean_dec(x_2);
x_282 = lean_ctor_get(x_278, 3);
lean_inc(x_282);
lean_dec(x_278);
x_283 = lean_nat_add(x_282, x_280);
lean_dec(x_280);
lean_dec(x_282);
x_284 = lean_array_get_size(x_279);
x_285 = lean_nat_dec_lt(x_283, x_284);
lean_dec(x_284);
x_286 = l_List_isEmpty___rarg(x_281);
if (x_285 == 0)
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_283);
lean_dec(x_279);
x_295 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_296 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_295);
x_287 = x_296;
goto block_294;
}
else
{
lean_object* x_297; 
x_297 = lean_array_fget(x_279, x_283);
lean_dec(x_283);
lean_dec(x_279);
x_287 = x_297;
goto block_294;
}
block_294:
{
if (x_286 == 0)
{
lean_dec(x_275);
lean_dec(x_207);
x_1 = x_287;
x_2 = x_281;
x_9 = x_206;
goto _start;
}
else
{
lean_dec(x_281);
if (lean_obj_tag(x_287) == 1)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
if (lean_is_scalar(x_275)) {
 x_290 = lean_alloc_ctor(1, 1, 0);
} else {
 x_290 = x_275;
}
lean_ctor_set(x_290, 0, x_289);
if (lean_is_scalar(x_207)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_207;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_206);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_287);
lean_dec(x_275);
lean_dec(x_207);
x_292 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_293 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_292, x_3, x_4, x_5, x_6, x_7, x_8, x_206);
return x_293;
}
}
}
}
}
}
case 3:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_298 = lean_ctor_get(x_11, 1);
lean_inc(x_298);
lean_dec(x_11);
x_299 = lean_st_ref_get(x_8, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
lean_dec(x_300);
lean_inc(x_12);
x_304 = l_Lean_Expr_constructorApp_x3f(x_303, x_12);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_305) == 4)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_302);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_8);
lean_inc(x_7);
x_308 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_306, x_7, x_8, x_301);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
lean_dec(x_307);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_310 = !lean_is_exclusive(x_308);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_308, 0);
lean_dec(x_311);
x_312 = lean_box(0);
lean_ctor_set(x_308, 0, x_312);
return x_308;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_dec(x_308);
x_314 = lean_box(0);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_308);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_317 = lean_ctor_get(x_308, 1);
x_318 = lean_ctor_get(x_308, 0);
lean_dec(x_318);
x_319 = lean_ctor_get(x_309, 0);
lean_inc(x_319);
lean_dec(x_309);
x_320 = l_Lean_Compiler_LCNF_Decl_getArity(x_319);
x_321 = lean_unsigned_to_nat(0u);
x_322 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_321);
x_323 = lean_nat_dec_eq(x_320, x_322);
lean_dec(x_320);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_307);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_324 = lean_box(0);
lean_ctor_set(x_308, 0, x_324);
return x_308;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_free_object(x_308);
lean_inc(x_319);
x_325 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_319, x_307);
x_326 = lean_ctor_get(x_319, 3);
lean_inc(x_326);
lean_dec(x_319);
x_327 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_322);
x_328 = lean_mk_array(x_322, x_327);
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_nat_sub(x_322, x_329);
lean_dec(x_322);
x_331 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_328, x_330);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_332 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_326, x_325, x_331, x_10, x_4, x_5, x_6, x_7, x_8, x_317);
lean_dec(x_326);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_333, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_334);
return x_335;
}
else
{
uint8_t x_336; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_336 = !lean_is_exclusive(x_332);
if (x_336 == 0)
{
return x_332;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_332, 0);
x_338 = lean_ctor_get(x_332, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_332);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_340 = lean_ctor_get(x_308, 1);
lean_inc(x_340);
lean_dec(x_308);
x_341 = lean_ctor_get(x_309, 0);
lean_inc(x_341);
lean_dec(x_309);
x_342 = l_Lean_Compiler_LCNF_Decl_getArity(x_341);
x_343 = lean_unsigned_to_nat(0u);
x_344 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_343);
x_345 = lean_nat_dec_eq(x_342, x_344);
lean_dec(x_342);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_344);
lean_dec(x_341);
lean_dec(x_307);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_340);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_inc(x_341);
x_348 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_341, x_307);
x_349 = lean_ctor_get(x_341, 3);
lean_inc(x_349);
lean_dec(x_341);
x_350 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_344);
x_351 = lean_mk_array(x_344, x_350);
x_352 = lean_unsigned_to_nat(1u);
x_353 = lean_nat_sub(x_344, x_352);
lean_dec(x_344);
x_354 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_351, x_353);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_355 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_349, x_348, x_354, x_10, x_4, x_5, x_6, x_7, x_8, x_340);
lean_dec(x_349);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_356, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_357);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = lean_ctor_get(x_355, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_355, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_361 = x_355;
} else {
 lean_dec_ref(x_355);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
}
}
else
{
uint8_t x_363; 
lean_dec(x_307);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_363 = !lean_is_exclusive(x_308);
if (x_363 == 0)
{
return x_308;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_308, 0);
x_365 = lean_ctor_get(x_308, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_308);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_305);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_367 = lean_box(0);
if (lean_is_scalar(x_302)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_302;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_301);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_12);
x_369 = lean_ctor_get(x_304, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_370 = x_304;
} else {
 lean_dec_ref(x_304);
 x_370 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_302);
x_371 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_372 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_371, x_3, x_4, x_5, x_6, x_7, x_8, x_301);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_381; lean_object* x_382; 
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
lean_dec(x_369);
x_375 = lean_ctor_get(x_2, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_2, 1);
lean_inc(x_376);
lean_dec(x_2);
x_377 = lean_ctor_get(x_373, 3);
lean_inc(x_377);
lean_dec(x_373);
x_378 = lean_nat_add(x_377, x_375);
lean_dec(x_375);
lean_dec(x_377);
x_379 = lean_array_get_size(x_374);
x_380 = lean_nat_dec_lt(x_378, x_379);
lean_dec(x_379);
x_381 = l_List_isEmpty___rarg(x_376);
if (x_380 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_378);
lean_dec(x_374);
x_390 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_391 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_390);
x_382 = x_391;
goto block_389;
}
else
{
lean_object* x_392; 
x_392 = lean_array_fget(x_374, x_378);
lean_dec(x_378);
lean_dec(x_374);
x_382 = x_392;
goto block_389;
}
block_389:
{
if (x_381 == 0)
{
lean_dec(x_370);
lean_dec(x_302);
x_1 = x_382;
x_2 = x_376;
x_9 = x_301;
goto _start;
}
else
{
lean_dec(x_376);
if (lean_obj_tag(x_382) == 1)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
lean_dec(x_382);
if (lean_is_scalar(x_370)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_370;
}
lean_ctor_set(x_385, 0, x_384);
if (lean_is_scalar(x_302)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_302;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_301);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_382);
lean_dec(x_370);
lean_dec(x_302);
x_387 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_388 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_387, x_3, x_4, x_5, x_6, x_7, x_8, x_301);
return x_388;
}
}
}
}
}
}
case 4:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_393 = lean_ctor_get(x_11, 1);
lean_inc(x_393);
lean_dec(x_11);
x_394 = lean_st_ref_get(x_8, x_393);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_395, 0);
lean_inc(x_398);
lean_dec(x_395);
lean_inc(x_12);
x_399 = l_Lean_Expr_constructorApp_x3f(x_398, x_12);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
x_400 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_400) == 4)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_397);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
lean_inc(x_8);
lean_inc(x_7);
x_403 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_401, x_7, x_8, x_396);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
uint8_t x_405; 
lean_dec(x_402);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_405 = !lean_is_exclusive(x_403);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_403, 0);
lean_dec(x_406);
x_407 = lean_box(0);
lean_ctor_set(x_403, 0, x_407);
return x_403;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_403, 1);
lean_inc(x_408);
lean_dec(x_403);
x_409 = lean_box(0);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_403);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_412 = lean_ctor_get(x_403, 1);
x_413 = lean_ctor_get(x_403, 0);
lean_dec(x_413);
x_414 = lean_ctor_get(x_404, 0);
lean_inc(x_414);
lean_dec(x_404);
x_415 = l_Lean_Compiler_LCNF_Decl_getArity(x_414);
x_416 = lean_unsigned_to_nat(0u);
x_417 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_416);
x_418 = lean_nat_dec_eq(x_415, x_417);
lean_dec(x_415);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_402);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_419 = lean_box(0);
lean_ctor_set(x_403, 0, x_419);
return x_403;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_free_object(x_403);
lean_inc(x_414);
x_420 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_414, x_402);
x_421 = lean_ctor_get(x_414, 3);
lean_inc(x_421);
lean_dec(x_414);
x_422 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_417);
x_423 = lean_mk_array(x_417, x_422);
x_424 = lean_unsigned_to_nat(1u);
x_425 = lean_nat_sub(x_417, x_424);
lean_dec(x_417);
x_426 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_423, x_425);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_427 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_421, x_420, x_426, x_10, x_4, x_5, x_6, x_7, x_8, x_412);
lean_dec(x_421);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_428, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
return x_430;
}
else
{
uint8_t x_431; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_431 = !lean_is_exclusive(x_427);
if (x_431 == 0)
{
return x_427;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_427, 0);
x_433 = lean_ctor_get(x_427, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_427);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_435 = lean_ctor_get(x_403, 1);
lean_inc(x_435);
lean_dec(x_403);
x_436 = lean_ctor_get(x_404, 0);
lean_inc(x_436);
lean_dec(x_404);
x_437 = l_Lean_Compiler_LCNF_Decl_getArity(x_436);
x_438 = lean_unsigned_to_nat(0u);
x_439 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_438);
x_440 = lean_nat_dec_eq(x_437, x_439);
lean_dec(x_437);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_439);
lean_dec(x_436);
lean_dec(x_402);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_441 = lean_box(0);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_435);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_inc(x_436);
x_443 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_436, x_402);
x_444 = lean_ctor_get(x_436, 3);
lean_inc(x_444);
lean_dec(x_436);
x_445 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_439);
x_446 = lean_mk_array(x_439, x_445);
x_447 = lean_unsigned_to_nat(1u);
x_448 = lean_nat_sub(x_439, x_447);
lean_dec(x_439);
x_449 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_446, x_448);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_450 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_444, x_443, x_449, x_10, x_4, x_5, x_6, x_7, x_8, x_435);
lean_dec(x_444);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_451, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_452);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_454 = lean_ctor_get(x_450, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_450, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_456 = x_450;
} else {
 lean_dec_ref(x_450);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_402);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_458 = !lean_is_exclusive(x_403);
if (x_458 == 0)
{
return x_403;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_403, 0);
x_460 = lean_ctor_get(x_403, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_403);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; 
lean_dec(x_400);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_462 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_397;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_396);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_12);
x_464 = lean_ctor_get(x_399, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_465 = x_399;
} else {
 lean_dec_ref(x_399);
 x_465 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_397);
x_466 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_467 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_466, x_3, x_4, x_5, x_6, x_7, x_8, x_396);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_476; lean_object* x_477; 
x_468 = lean_ctor_get(x_464, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_464, 1);
lean_inc(x_469);
lean_dec(x_464);
x_470 = lean_ctor_get(x_2, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_2, 1);
lean_inc(x_471);
lean_dec(x_2);
x_472 = lean_ctor_get(x_468, 3);
lean_inc(x_472);
lean_dec(x_468);
x_473 = lean_nat_add(x_472, x_470);
lean_dec(x_470);
lean_dec(x_472);
x_474 = lean_array_get_size(x_469);
x_475 = lean_nat_dec_lt(x_473, x_474);
lean_dec(x_474);
x_476 = l_List_isEmpty___rarg(x_471);
if (x_475 == 0)
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_473);
lean_dec(x_469);
x_485 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_486 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_485);
x_477 = x_486;
goto block_484;
}
else
{
lean_object* x_487; 
x_487 = lean_array_fget(x_469, x_473);
lean_dec(x_473);
lean_dec(x_469);
x_477 = x_487;
goto block_484;
}
block_484:
{
if (x_476 == 0)
{
lean_dec(x_465);
lean_dec(x_397);
x_1 = x_477;
x_2 = x_471;
x_9 = x_396;
goto _start;
}
else
{
lean_dec(x_471);
if (lean_obj_tag(x_477) == 1)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
lean_dec(x_477);
if (lean_is_scalar(x_465)) {
 x_480 = lean_alloc_ctor(1, 1, 0);
} else {
 x_480 = x_465;
}
lean_ctor_set(x_480, 0, x_479);
if (lean_is_scalar(x_397)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_397;
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_396);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_477);
lean_dec(x_465);
lean_dec(x_397);
x_482 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_483 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_482, x_3, x_4, x_5, x_6, x_7, x_8, x_396);
return x_483;
}
}
}
}
}
}
case 5:
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_11, 1);
lean_inc(x_488);
lean_dec(x_11);
x_489 = lean_st_ref_get(x_8, x_488);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_492 = x_489;
} else {
 lean_dec_ref(x_489);
 x_492 = lean_box(0);
}
x_493 = lean_ctor_get(x_490, 0);
lean_inc(x_493);
lean_dec(x_490);
lean_inc(x_12);
x_494 = l_Lean_Expr_constructorApp_x3f(x_493, x_12);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; 
x_495 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_495) == 4)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_492);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
lean_inc(x_8);
lean_inc(x_7);
x_498 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_496, x_7, x_8, x_491);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_obj_tag(x_499) == 0)
{
uint8_t x_500; 
lean_dec(x_497);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_500 = !lean_is_exclusive(x_498);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_ctor_get(x_498, 0);
lean_dec(x_501);
x_502 = lean_box(0);
lean_ctor_set(x_498, 0, x_502);
return x_498;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_498, 1);
lean_inc(x_503);
lean_dec(x_498);
x_504 = lean_box(0);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
uint8_t x_506; 
x_506 = !lean_is_exclusive(x_498);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_507 = lean_ctor_get(x_498, 1);
x_508 = lean_ctor_get(x_498, 0);
lean_dec(x_508);
x_509 = lean_ctor_get(x_499, 0);
lean_inc(x_509);
lean_dec(x_499);
x_510 = l_Lean_Compiler_LCNF_Decl_getArity(x_509);
x_511 = lean_unsigned_to_nat(0u);
x_512 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_511);
x_513 = lean_nat_dec_eq(x_510, x_512);
lean_dec(x_510);
if (x_513 == 0)
{
lean_object* x_514; 
lean_dec(x_512);
lean_dec(x_509);
lean_dec(x_497);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_514 = lean_box(0);
lean_ctor_set(x_498, 0, x_514);
return x_498;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_free_object(x_498);
lean_inc(x_509);
x_515 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_509, x_497);
x_516 = lean_ctor_get(x_509, 3);
lean_inc(x_516);
lean_dec(x_509);
x_517 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_512);
x_518 = lean_mk_array(x_512, x_517);
x_519 = lean_unsigned_to_nat(1u);
x_520 = lean_nat_sub(x_512, x_519);
lean_dec(x_512);
x_521 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_518, x_520);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_522 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_516, x_515, x_521, x_10, x_4, x_5, x_6, x_7, x_8, x_507);
lean_dec(x_516);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_523, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_524);
return x_525;
}
else
{
uint8_t x_526; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_526 = !lean_is_exclusive(x_522);
if (x_526 == 0)
{
return x_522;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_522, 0);
x_528 = lean_ctor_get(x_522, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_522);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_530 = lean_ctor_get(x_498, 1);
lean_inc(x_530);
lean_dec(x_498);
x_531 = lean_ctor_get(x_499, 0);
lean_inc(x_531);
lean_dec(x_499);
x_532 = l_Lean_Compiler_LCNF_Decl_getArity(x_531);
x_533 = lean_unsigned_to_nat(0u);
x_534 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_533);
x_535 = lean_nat_dec_eq(x_532, x_534);
lean_dec(x_532);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_534);
lean_dec(x_531);
lean_dec(x_497);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_536 = lean_box(0);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_530);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_inc(x_531);
x_538 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_531, x_497);
x_539 = lean_ctor_get(x_531, 3);
lean_inc(x_539);
lean_dec(x_531);
x_540 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_534);
x_541 = lean_mk_array(x_534, x_540);
x_542 = lean_unsigned_to_nat(1u);
x_543 = lean_nat_sub(x_534, x_542);
lean_dec(x_534);
x_544 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_541, x_543);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_545 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_539, x_538, x_544, x_10, x_4, x_5, x_6, x_7, x_8, x_530);
lean_dec(x_539);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_546, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_547);
return x_548;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_549 = lean_ctor_get(x_545, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_545, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_551 = x_545;
} else {
 lean_dec_ref(x_545);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
}
}
}
else
{
uint8_t x_553; 
lean_dec(x_497);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_553 = !lean_is_exclusive(x_498);
if (x_553 == 0)
{
return x_498;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_498, 0);
x_555 = lean_ctor_get(x_498, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_498);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_495);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_557 = lean_box(0);
if (lean_is_scalar(x_492)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_492;
}
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_491);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; 
lean_dec(x_12);
x_559 = lean_ctor_get(x_494, 0);
lean_inc(x_559);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_560 = x_494;
} else {
 lean_dec_ref(x_494);
 x_560 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_492);
x_561 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_562 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_561, x_3, x_4, x_5, x_6, x_7, x_8, x_491);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_571; lean_object* x_572; 
x_563 = lean_ctor_get(x_559, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_559, 1);
lean_inc(x_564);
lean_dec(x_559);
x_565 = lean_ctor_get(x_2, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_2, 1);
lean_inc(x_566);
lean_dec(x_2);
x_567 = lean_ctor_get(x_563, 3);
lean_inc(x_567);
lean_dec(x_563);
x_568 = lean_nat_add(x_567, x_565);
lean_dec(x_565);
lean_dec(x_567);
x_569 = lean_array_get_size(x_564);
x_570 = lean_nat_dec_lt(x_568, x_569);
lean_dec(x_569);
x_571 = l_List_isEmpty___rarg(x_566);
if (x_570 == 0)
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_568);
lean_dec(x_564);
x_580 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_581 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_580);
x_572 = x_581;
goto block_579;
}
else
{
lean_object* x_582; 
x_582 = lean_array_fget(x_564, x_568);
lean_dec(x_568);
lean_dec(x_564);
x_572 = x_582;
goto block_579;
}
block_579:
{
if (x_571 == 0)
{
lean_dec(x_560);
lean_dec(x_492);
x_1 = x_572;
x_2 = x_566;
x_9 = x_491;
goto _start;
}
else
{
lean_dec(x_566);
if (lean_obj_tag(x_572) == 1)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_574 = lean_ctor_get(x_572, 0);
lean_inc(x_574);
lean_dec(x_572);
if (lean_is_scalar(x_560)) {
 x_575 = lean_alloc_ctor(1, 1, 0);
} else {
 x_575 = x_560;
}
lean_ctor_set(x_575, 0, x_574);
if (lean_is_scalar(x_492)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_492;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_491);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_572);
lean_dec(x_560);
lean_dec(x_492);
x_577 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_578 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_577, x_3, x_4, x_5, x_6, x_7, x_8, x_491);
return x_578;
}
}
}
}
}
}
case 6:
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_583 = lean_ctor_get(x_11, 1);
lean_inc(x_583);
lean_dec(x_11);
x_584 = lean_st_ref_get(x_8, x_583);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_587 = x_584;
} else {
 lean_dec_ref(x_584);
 x_587 = lean_box(0);
}
x_588 = lean_ctor_get(x_585, 0);
lean_inc(x_588);
lean_dec(x_585);
lean_inc(x_12);
x_589 = l_Lean_Expr_constructorApp_x3f(x_588, x_12);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
x_590 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_590) == 4)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_587);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
lean_inc(x_8);
lean_inc(x_7);
x_593 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_591, x_7, x_8, x_586);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
if (lean_obj_tag(x_594) == 0)
{
uint8_t x_595; 
lean_dec(x_592);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_595 = !lean_is_exclusive(x_593);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_ctor_get(x_593, 0);
lean_dec(x_596);
x_597 = lean_box(0);
lean_ctor_set(x_593, 0, x_597);
return x_593;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_593, 1);
lean_inc(x_598);
lean_dec(x_593);
x_599 = lean_box(0);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
uint8_t x_601; 
x_601 = !lean_is_exclusive(x_593);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
x_602 = lean_ctor_get(x_593, 1);
x_603 = lean_ctor_get(x_593, 0);
lean_dec(x_603);
x_604 = lean_ctor_get(x_594, 0);
lean_inc(x_604);
lean_dec(x_594);
x_605 = l_Lean_Compiler_LCNF_Decl_getArity(x_604);
x_606 = lean_unsigned_to_nat(0u);
x_607 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_606);
x_608 = lean_nat_dec_eq(x_605, x_607);
lean_dec(x_605);
if (x_608 == 0)
{
lean_object* x_609; 
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_592);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_609 = lean_box(0);
lean_ctor_set(x_593, 0, x_609);
return x_593;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_free_object(x_593);
lean_inc(x_604);
x_610 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_604, x_592);
x_611 = lean_ctor_get(x_604, 3);
lean_inc(x_611);
lean_dec(x_604);
x_612 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_607);
x_613 = lean_mk_array(x_607, x_612);
x_614 = lean_unsigned_to_nat(1u);
x_615 = lean_nat_sub(x_607, x_614);
lean_dec(x_607);
x_616 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_613, x_615);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_617 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_611, x_610, x_616, x_10, x_4, x_5, x_6, x_7, x_8, x_602);
lean_dec(x_611);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_618, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_619);
return x_620;
}
else
{
uint8_t x_621; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_621 = !lean_is_exclusive(x_617);
if (x_621 == 0)
{
return x_617;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_617, 0);
x_623 = lean_ctor_get(x_617, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_617);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
return x_624;
}
}
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_625 = lean_ctor_get(x_593, 1);
lean_inc(x_625);
lean_dec(x_593);
x_626 = lean_ctor_get(x_594, 0);
lean_inc(x_626);
lean_dec(x_594);
x_627 = l_Lean_Compiler_LCNF_Decl_getArity(x_626);
x_628 = lean_unsigned_to_nat(0u);
x_629 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_628);
x_630 = lean_nat_dec_eq(x_627, x_629);
lean_dec(x_627);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
lean_dec(x_629);
lean_dec(x_626);
lean_dec(x_592);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_631 = lean_box(0);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_625);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_inc(x_626);
x_633 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_626, x_592);
x_634 = lean_ctor_get(x_626, 3);
lean_inc(x_634);
lean_dec(x_626);
x_635 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_629);
x_636 = lean_mk_array(x_629, x_635);
x_637 = lean_unsigned_to_nat(1u);
x_638 = lean_nat_sub(x_629, x_637);
lean_dec(x_629);
x_639 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_636, x_638);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_640 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_634, x_633, x_639, x_10, x_4, x_5, x_6, x_7, x_8, x_625);
lean_dec(x_634);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_641, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_642);
return x_643;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_644 = lean_ctor_get(x_640, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_640, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_646 = x_640;
} else {
 lean_dec_ref(x_640);
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
}
}
}
else
{
uint8_t x_648; 
lean_dec(x_592);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_648 = !lean_is_exclusive(x_593);
if (x_648 == 0)
{
return x_593;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_593, 0);
x_650 = lean_ctor_get(x_593, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_593);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
lean_dec(x_590);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_652 = lean_box(0);
if (lean_is_scalar(x_587)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_587;
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_586);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; 
lean_dec(x_12);
x_654 = lean_ctor_get(x_589, 0);
lean_inc(x_654);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_655 = x_589;
} else {
 lean_dec_ref(x_589);
 x_655 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_587);
x_656 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_657 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_656, x_3, x_4, x_5, x_6, x_7, x_8, x_586);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_666; lean_object* x_667; 
x_658 = lean_ctor_get(x_654, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_654, 1);
lean_inc(x_659);
lean_dec(x_654);
x_660 = lean_ctor_get(x_2, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_2, 1);
lean_inc(x_661);
lean_dec(x_2);
x_662 = lean_ctor_get(x_658, 3);
lean_inc(x_662);
lean_dec(x_658);
x_663 = lean_nat_add(x_662, x_660);
lean_dec(x_660);
lean_dec(x_662);
x_664 = lean_array_get_size(x_659);
x_665 = lean_nat_dec_lt(x_663, x_664);
lean_dec(x_664);
x_666 = l_List_isEmpty___rarg(x_661);
if (x_665 == 0)
{
lean_object* x_675; lean_object* x_676; 
lean_dec(x_663);
lean_dec(x_659);
x_675 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_676 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_675);
x_667 = x_676;
goto block_674;
}
else
{
lean_object* x_677; 
x_677 = lean_array_fget(x_659, x_663);
lean_dec(x_663);
lean_dec(x_659);
x_667 = x_677;
goto block_674;
}
block_674:
{
if (x_666 == 0)
{
lean_dec(x_655);
lean_dec(x_587);
x_1 = x_667;
x_2 = x_661;
x_9 = x_586;
goto _start;
}
else
{
lean_dec(x_661);
if (lean_obj_tag(x_667) == 1)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_669 = lean_ctor_get(x_667, 0);
lean_inc(x_669);
lean_dec(x_667);
if (lean_is_scalar(x_655)) {
 x_670 = lean_alloc_ctor(1, 1, 0);
} else {
 x_670 = x_655;
}
lean_ctor_set(x_670, 0, x_669);
if (lean_is_scalar(x_587)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_587;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_586);
return x_671;
}
else
{
lean_object* x_672; lean_object* x_673; 
lean_dec(x_667);
lean_dec(x_655);
lean_dec(x_587);
x_672 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_673 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_672, x_3, x_4, x_5, x_6, x_7, x_8, x_586);
return x_673;
}
}
}
}
}
}
case 7:
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_678 = lean_ctor_get(x_11, 1);
lean_inc(x_678);
lean_dec(x_11);
x_679 = lean_st_ref_get(x_8, x_678);
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
x_683 = lean_ctor_get(x_680, 0);
lean_inc(x_683);
lean_dec(x_680);
lean_inc(x_12);
x_684 = l_Lean_Expr_constructorApp_x3f(x_683, x_12);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
x_685 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_685) == 4)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_682);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
lean_inc(x_8);
lean_inc(x_7);
x_688 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_686, x_7, x_8, x_681);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_obj_tag(x_689) == 0)
{
uint8_t x_690; 
lean_dec(x_687);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_690 = !lean_is_exclusive(x_688);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; 
x_691 = lean_ctor_get(x_688, 0);
lean_dec(x_691);
x_692 = lean_box(0);
lean_ctor_set(x_688, 0, x_692);
return x_688;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_688, 1);
lean_inc(x_693);
lean_dec(x_688);
x_694 = lean_box(0);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
else
{
uint8_t x_696; 
x_696 = !lean_is_exclusive(x_688);
if (x_696 == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_697 = lean_ctor_get(x_688, 1);
x_698 = lean_ctor_get(x_688, 0);
lean_dec(x_698);
x_699 = lean_ctor_get(x_689, 0);
lean_inc(x_699);
lean_dec(x_689);
x_700 = l_Lean_Compiler_LCNF_Decl_getArity(x_699);
x_701 = lean_unsigned_to_nat(0u);
x_702 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_701);
x_703 = lean_nat_dec_eq(x_700, x_702);
lean_dec(x_700);
if (x_703 == 0)
{
lean_object* x_704; 
lean_dec(x_702);
lean_dec(x_699);
lean_dec(x_687);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_704 = lean_box(0);
lean_ctor_set(x_688, 0, x_704);
return x_688;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_free_object(x_688);
lean_inc(x_699);
x_705 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_699, x_687);
x_706 = lean_ctor_get(x_699, 3);
lean_inc(x_706);
lean_dec(x_699);
x_707 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_702);
x_708 = lean_mk_array(x_702, x_707);
x_709 = lean_unsigned_to_nat(1u);
x_710 = lean_nat_sub(x_702, x_709);
lean_dec(x_702);
x_711 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_708, x_710);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_712 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_706, x_705, x_711, x_10, x_4, x_5, x_6, x_7, x_8, x_697);
lean_dec(x_706);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_713, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_714);
return x_715;
}
else
{
uint8_t x_716; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_716 = !lean_is_exclusive(x_712);
if (x_716 == 0)
{
return x_712;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_712, 0);
x_718 = lean_ctor_get(x_712, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_712);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_720 = lean_ctor_get(x_688, 1);
lean_inc(x_720);
lean_dec(x_688);
x_721 = lean_ctor_get(x_689, 0);
lean_inc(x_721);
lean_dec(x_689);
x_722 = l_Lean_Compiler_LCNF_Decl_getArity(x_721);
x_723 = lean_unsigned_to_nat(0u);
x_724 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_723);
x_725 = lean_nat_dec_eq(x_722, x_724);
lean_dec(x_722);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; 
lean_dec(x_724);
lean_dec(x_721);
lean_dec(x_687);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_726 = lean_box(0);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_720);
return x_727;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_inc(x_721);
x_728 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_721, x_687);
x_729 = lean_ctor_get(x_721, 3);
lean_inc(x_729);
lean_dec(x_721);
x_730 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_724);
x_731 = lean_mk_array(x_724, x_730);
x_732 = lean_unsigned_to_nat(1u);
x_733 = lean_nat_sub(x_724, x_732);
lean_dec(x_724);
x_734 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_731, x_733);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_735 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_729, x_728, x_734, x_10, x_4, x_5, x_6, x_7, x_8, x_720);
lean_dec(x_729);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_736, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_737);
return x_738;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_739 = lean_ctor_get(x_735, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_735, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_741 = x_735;
} else {
 lean_dec_ref(x_735);
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
}
}
}
else
{
uint8_t x_743; 
lean_dec(x_687);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_743 = !lean_is_exclusive(x_688);
if (x_743 == 0)
{
return x_688;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_688, 0);
x_745 = lean_ctor_get(x_688, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_688);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
}
}
}
else
{
lean_object* x_747; lean_object* x_748; 
lean_dec(x_685);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_747 = lean_box(0);
if (lean_is_scalar(x_682)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_682;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_681);
return x_748;
}
}
else
{
lean_object* x_749; lean_object* x_750; 
lean_dec(x_12);
x_749 = lean_ctor_get(x_684, 0);
lean_inc(x_749);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 x_750 = x_684;
} else {
 lean_dec_ref(x_684);
 x_750 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_751; lean_object* x_752; 
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_682);
x_751 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_752 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_751, x_3, x_4, x_5, x_6, x_7, x_8, x_681);
return x_752;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; uint8_t x_761; lean_object* x_762; 
x_753 = lean_ctor_get(x_749, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_749, 1);
lean_inc(x_754);
lean_dec(x_749);
x_755 = lean_ctor_get(x_2, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_2, 1);
lean_inc(x_756);
lean_dec(x_2);
x_757 = lean_ctor_get(x_753, 3);
lean_inc(x_757);
lean_dec(x_753);
x_758 = lean_nat_add(x_757, x_755);
lean_dec(x_755);
lean_dec(x_757);
x_759 = lean_array_get_size(x_754);
x_760 = lean_nat_dec_lt(x_758, x_759);
lean_dec(x_759);
x_761 = l_List_isEmpty___rarg(x_756);
if (x_760 == 0)
{
lean_object* x_770; lean_object* x_771; 
lean_dec(x_758);
lean_dec(x_754);
x_770 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_771 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_770);
x_762 = x_771;
goto block_769;
}
else
{
lean_object* x_772; 
x_772 = lean_array_fget(x_754, x_758);
lean_dec(x_758);
lean_dec(x_754);
x_762 = x_772;
goto block_769;
}
block_769:
{
if (x_761 == 0)
{
lean_dec(x_750);
lean_dec(x_682);
x_1 = x_762;
x_2 = x_756;
x_9 = x_681;
goto _start;
}
else
{
lean_dec(x_756);
if (lean_obj_tag(x_762) == 1)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_764 = lean_ctor_get(x_762, 0);
lean_inc(x_764);
lean_dec(x_762);
if (lean_is_scalar(x_750)) {
 x_765 = lean_alloc_ctor(1, 1, 0);
} else {
 x_765 = x_750;
}
lean_ctor_set(x_765, 0, x_764);
if (lean_is_scalar(x_682)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_682;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_681);
return x_766;
}
else
{
lean_object* x_767; lean_object* x_768; 
lean_dec(x_762);
lean_dec(x_750);
lean_dec(x_682);
x_767 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_768 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_767, x_3, x_4, x_5, x_6, x_7, x_8, x_681);
return x_768;
}
}
}
}
}
}
case 8:
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_773 = lean_ctor_get(x_11, 1);
lean_inc(x_773);
lean_dec(x_11);
x_774 = lean_st_ref_get(x_8, x_773);
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_777 = x_774;
} else {
 lean_dec_ref(x_774);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_775, 0);
lean_inc(x_778);
lean_dec(x_775);
lean_inc(x_12);
x_779 = l_Lean_Expr_constructorApp_x3f(x_778, x_12);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; 
x_780 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_780) == 4)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_777);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
lean_inc(x_8);
lean_inc(x_7);
x_783 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_781, x_7, x_8, x_776);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
if (lean_obj_tag(x_784) == 0)
{
uint8_t x_785; 
lean_dec(x_782);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_785 = !lean_is_exclusive(x_783);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_783, 0);
lean_dec(x_786);
x_787 = lean_box(0);
lean_ctor_set(x_783, 0, x_787);
return x_783;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_783, 1);
lean_inc(x_788);
lean_dec(x_783);
x_789 = lean_box(0);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
}
else
{
uint8_t x_791; 
x_791 = !lean_is_exclusive(x_783);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; 
x_792 = lean_ctor_get(x_783, 1);
x_793 = lean_ctor_get(x_783, 0);
lean_dec(x_793);
x_794 = lean_ctor_get(x_784, 0);
lean_inc(x_794);
lean_dec(x_784);
x_795 = l_Lean_Compiler_LCNF_Decl_getArity(x_794);
x_796 = lean_unsigned_to_nat(0u);
x_797 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_796);
x_798 = lean_nat_dec_eq(x_795, x_797);
lean_dec(x_795);
if (x_798 == 0)
{
lean_object* x_799; 
lean_dec(x_797);
lean_dec(x_794);
lean_dec(x_782);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_799 = lean_box(0);
lean_ctor_set(x_783, 0, x_799);
return x_783;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_free_object(x_783);
lean_inc(x_794);
x_800 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_794, x_782);
x_801 = lean_ctor_get(x_794, 3);
lean_inc(x_801);
lean_dec(x_794);
x_802 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_797);
x_803 = lean_mk_array(x_797, x_802);
x_804 = lean_unsigned_to_nat(1u);
x_805 = lean_nat_sub(x_797, x_804);
lean_dec(x_797);
x_806 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_803, x_805);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_807 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_801, x_800, x_806, x_10, x_4, x_5, x_6, x_7, x_8, x_792);
lean_dec(x_801);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_808, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_809);
return x_810;
}
else
{
uint8_t x_811; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_811 = !lean_is_exclusive(x_807);
if (x_811 == 0)
{
return x_807;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_807, 0);
x_813 = lean_ctor_get(x_807, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_807);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
return x_814;
}
}
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
x_815 = lean_ctor_get(x_783, 1);
lean_inc(x_815);
lean_dec(x_783);
x_816 = lean_ctor_get(x_784, 0);
lean_inc(x_816);
lean_dec(x_784);
x_817 = l_Lean_Compiler_LCNF_Decl_getArity(x_816);
x_818 = lean_unsigned_to_nat(0u);
x_819 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_818);
x_820 = lean_nat_dec_eq(x_817, x_819);
lean_dec(x_817);
if (x_820 == 0)
{
lean_object* x_821; lean_object* x_822; 
lean_dec(x_819);
lean_dec(x_816);
lean_dec(x_782);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_821 = lean_box(0);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_815);
return x_822;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_inc(x_816);
x_823 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_816, x_782);
x_824 = lean_ctor_get(x_816, 3);
lean_inc(x_824);
lean_dec(x_816);
x_825 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_819);
x_826 = lean_mk_array(x_819, x_825);
x_827 = lean_unsigned_to_nat(1u);
x_828 = lean_nat_sub(x_819, x_827);
lean_dec(x_819);
x_829 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_826, x_828);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_830 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_824, x_823, x_829, x_10, x_4, x_5, x_6, x_7, x_8, x_815);
lean_dec(x_824);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
x_833 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_831, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_832);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_834 = lean_ctor_get(x_830, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_830, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_836 = x_830;
} else {
 lean_dec_ref(x_830);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(1, 2, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_834);
lean_ctor_set(x_837, 1, x_835);
return x_837;
}
}
}
}
}
else
{
uint8_t x_838; 
lean_dec(x_782);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_838 = !lean_is_exclusive(x_783);
if (x_838 == 0)
{
return x_783;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_783, 0);
x_840 = lean_ctor_get(x_783, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_783);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
lean_object* x_842; lean_object* x_843; 
lean_dec(x_780);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_842 = lean_box(0);
if (lean_is_scalar(x_777)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_777;
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_776);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; 
lean_dec(x_12);
x_844 = lean_ctor_get(x_779, 0);
lean_inc(x_844);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 x_845 = x_779;
} else {
 lean_dec_ref(x_779);
 x_845 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_846; lean_object* x_847; 
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_777);
x_846 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_847 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_846, x_3, x_4, x_5, x_6, x_7, x_8, x_776);
return x_847;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; uint8_t x_856; lean_object* x_857; 
x_848 = lean_ctor_get(x_844, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_844, 1);
lean_inc(x_849);
lean_dec(x_844);
x_850 = lean_ctor_get(x_2, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_2, 1);
lean_inc(x_851);
lean_dec(x_2);
x_852 = lean_ctor_get(x_848, 3);
lean_inc(x_852);
lean_dec(x_848);
x_853 = lean_nat_add(x_852, x_850);
lean_dec(x_850);
lean_dec(x_852);
x_854 = lean_array_get_size(x_849);
x_855 = lean_nat_dec_lt(x_853, x_854);
lean_dec(x_854);
x_856 = l_List_isEmpty___rarg(x_851);
if (x_855 == 0)
{
lean_object* x_865; lean_object* x_866; 
lean_dec(x_853);
lean_dec(x_849);
x_865 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_866 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_865);
x_857 = x_866;
goto block_864;
}
else
{
lean_object* x_867; 
x_867 = lean_array_fget(x_849, x_853);
lean_dec(x_853);
lean_dec(x_849);
x_857 = x_867;
goto block_864;
}
block_864:
{
if (x_856 == 0)
{
lean_dec(x_845);
lean_dec(x_777);
x_1 = x_857;
x_2 = x_851;
x_9 = x_776;
goto _start;
}
else
{
lean_dec(x_851);
if (lean_obj_tag(x_857) == 1)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_859 = lean_ctor_get(x_857, 0);
lean_inc(x_859);
lean_dec(x_857);
if (lean_is_scalar(x_845)) {
 x_860 = lean_alloc_ctor(1, 1, 0);
} else {
 x_860 = x_845;
}
lean_ctor_set(x_860, 0, x_859);
if (lean_is_scalar(x_777)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_777;
}
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_776);
return x_861;
}
else
{
lean_object* x_862; lean_object* x_863; 
lean_dec(x_857);
lean_dec(x_845);
lean_dec(x_777);
x_862 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_863 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_862, x_3, x_4, x_5, x_6, x_7, x_8, x_776);
return x_863;
}
}
}
}
}
}
case 9:
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_868 = lean_ctor_get(x_11, 1);
lean_inc(x_868);
lean_dec(x_11);
x_869 = lean_st_ref_get(x_8, x_868);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_872 = x_869;
} else {
 lean_dec_ref(x_869);
 x_872 = lean_box(0);
}
x_873 = lean_ctor_get(x_870, 0);
lean_inc(x_873);
lean_dec(x_870);
lean_inc(x_12);
x_874 = l_Lean_Expr_constructorApp_x3f(x_873, x_12);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; 
x_875 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_875) == 4)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_872);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
lean_inc(x_8);
lean_inc(x_7);
x_878 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_876, x_7, x_8, x_871);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
if (lean_obj_tag(x_879) == 0)
{
uint8_t x_880; 
lean_dec(x_877);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_880 = !lean_is_exclusive(x_878);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; 
x_881 = lean_ctor_get(x_878, 0);
lean_dec(x_881);
x_882 = lean_box(0);
lean_ctor_set(x_878, 0, x_882);
return x_878;
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_883 = lean_ctor_get(x_878, 1);
lean_inc(x_883);
lean_dec(x_878);
x_884 = lean_box(0);
x_885 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_885, 0, x_884);
lean_ctor_set(x_885, 1, x_883);
return x_885;
}
}
else
{
uint8_t x_886; 
x_886 = !lean_is_exclusive(x_878);
if (x_886 == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_887 = lean_ctor_get(x_878, 1);
x_888 = lean_ctor_get(x_878, 0);
lean_dec(x_888);
x_889 = lean_ctor_get(x_879, 0);
lean_inc(x_889);
lean_dec(x_879);
x_890 = l_Lean_Compiler_LCNF_Decl_getArity(x_889);
x_891 = lean_unsigned_to_nat(0u);
x_892 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_891);
x_893 = lean_nat_dec_eq(x_890, x_892);
lean_dec(x_890);
if (x_893 == 0)
{
lean_object* x_894; 
lean_dec(x_892);
lean_dec(x_889);
lean_dec(x_877);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_894 = lean_box(0);
lean_ctor_set(x_878, 0, x_894);
return x_878;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_free_object(x_878);
lean_inc(x_889);
x_895 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_889, x_877);
x_896 = lean_ctor_get(x_889, 3);
lean_inc(x_896);
lean_dec(x_889);
x_897 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_892);
x_898 = lean_mk_array(x_892, x_897);
x_899 = lean_unsigned_to_nat(1u);
x_900 = lean_nat_sub(x_892, x_899);
lean_dec(x_892);
x_901 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_898, x_900);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_902 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_896, x_895, x_901, x_10, x_4, x_5, x_6, x_7, x_8, x_887);
lean_dec(x_896);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
x_905 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_903, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_904);
return x_905;
}
else
{
uint8_t x_906; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_906 = !lean_is_exclusive(x_902);
if (x_906 == 0)
{
return x_902;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_902, 0);
x_908 = lean_ctor_get(x_902, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_902);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_907);
lean_ctor_set(x_909, 1, x_908);
return x_909;
}
}
}
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; uint8_t x_915; 
x_910 = lean_ctor_get(x_878, 1);
lean_inc(x_910);
lean_dec(x_878);
x_911 = lean_ctor_get(x_879, 0);
lean_inc(x_911);
lean_dec(x_879);
x_912 = l_Lean_Compiler_LCNF_Decl_getArity(x_911);
x_913 = lean_unsigned_to_nat(0u);
x_914 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_913);
x_915 = lean_nat_dec_eq(x_912, x_914);
lean_dec(x_912);
if (x_915 == 0)
{
lean_object* x_916; lean_object* x_917; 
lean_dec(x_914);
lean_dec(x_911);
lean_dec(x_877);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_916 = lean_box(0);
x_917 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_917, 0, x_916);
lean_ctor_set(x_917, 1, x_910);
return x_917;
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_inc(x_911);
x_918 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_911, x_877);
x_919 = lean_ctor_get(x_911, 3);
lean_inc(x_919);
lean_dec(x_911);
x_920 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_914);
x_921 = lean_mk_array(x_914, x_920);
x_922 = lean_unsigned_to_nat(1u);
x_923 = lean_nat_sub(x_914, x_922);
lean_dec(x_914);
x_924 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_921, x_923);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_925 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_919, x_918, x_924, x_10, x_4, x_5, x_6, x_7, x_8, x_910);
lean_dec(x_919);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
x_928 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_926, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_927);
return x_928;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_929 = lean_ctor_get(x_925, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_925, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_931 = x_925;
} else {
 lean_dec_ref(x_925);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
return x_932;
}
}
}
}
}
else
{
uint8_t x_933; 
lean_dec(x_877);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_933 = !lean_is_exclusive(x_878);
if (x_933 == 0)
{
return x_878;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_934 = lean_ctor_get(x_878, 0);
x_935 = lean_ctor_get(x_878, 1);
lean_inc(x_935);
lean_inc(x_934);
lean_dec(x_878);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_934);
lean_ctor_set(x_936, 1, x_935);
return x_936;
}
}
}
else
{
lean_object* x_937; lean_object* x_938; 
lean_dec(x_875);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_937 = lean_box(0);
if (lean_is_scalar(x_872)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_872;
}
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_871);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; 
lean_dec(x_12);
x_939 = lean_ctor_get(x_874, 0);
lean_inc(x_939);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 x_940 = x_874;
} else {
 lean_dec_ref(x_874);
 x_940 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_941; lean_object* x_942; 
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_872);
x_941 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_942 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_941, x_3, x_4, x_5, x_6, x_7, x_8, x_871);
return x_942;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; uint8_t x_950; uint8_t x_951; lean_object* x_952; 
x_943 = lean_ctor_get(x_939, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_939, 1);
lean_inc(x_944);
lean_dec(x_939);
x_945 = lean_ctor_get(x_2, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_2, 1);
lean_inc(x_946);
lean_dec(x_2);
x_947 = lean_ctor_get(x_943, 3);
lean_inc(x_947);
lean_dec(x_943);
x_948 = lean_nat_add(x_947, x_945);
lean_dec(x_945);
lean_dec(x_947);
x_949 = lean_array_get_size(x_944);
x_950 = lean_nat_dec_lt(x_948, x_949);
lean_dec(x_949);
x_951 = l_List_isEmpty___rarg(x_946);
if (x_950 == 0)
{
lean_object* x_960; lean_object* x_961; 
lean_dec(x_948);
lean_dec(x_944);
x_960 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_961 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_960);
x_952 = x_961;
goto block_959;
}
else
{
lean_object* x_962; 
x_962 = lean_array_fget(x_944, x_948);
lean_dec(x_948);
lean_dec(x_944);
x_952 = x_962;
goto block_959;
}
block_959:
{
if (x_951 == 0)
{
lean_dec(x_940);
lean_dec(x_872);
x_1 = x_952;
x_2 = x_946;
x_9 = x_871;
goto _start;
}
else
{
lean_dec(x_946);
if (lean_obj_tag(x_952) == 1)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_954 = lean_ctor_get(x_952, 0);
lean_inc(x_954);
lean_dec(x_952);
if (lean_is_scalar(x_940)) {
 x_955 = lean_alloc_ctor(1, 1, 0);
} else {
 x_955 = x_940;
}
lean_ctor_set(x_955, 0, x_954);
if (lean_is_scalar(x_872)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_872;
}
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_871);
return x_956;
}
else
{
lean_object* x_957; lean_object* x_958; 
lean_dec(x_952);
lean_dec(x_940);
lean_dec(x_872);
x_957 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_958 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_957, x_3, x_4, x_5, x_6, x_7, x_8, x_871);
return x_958;
}
}
}
}
}
}
case 10:
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_963 = lean_ctor_get(x_11, 1);
lean_inc(x_963);
lean_dec(x_11);
x_964 = lean_st_ref_get(x_8, x_963);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_967 = x_964;
} else {
 lean_dec_ref(x_964);
 x_967 = lean_box(0);
}
x_968 = lean_ctor_get(x_965, 0);
lean_inc(x_968);
lean_dec(x_965);
lean_inc(x_12);
x_969 = l_Lean_Expr_constructorApp_x3f(x_968, x_12);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; 
x_970 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_970) == 4)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_967);
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
lean_inc(x_8);
lean_inc(x_7);
x_973 = l_Lean_Compiler_LCNF_getStage1Decl_x3f(x_971, x_7, x_8, x_966);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
if (lean_obj_tag(x_974) == 0)
{
uint8_t x_975; 
lean_dec(x_972);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_975 = !lean_is_exclusive(x_973);
if (x_975 == 0)
{
lean_object* x_976; lean_object* x_977; 
x_976 = lean_ctor_get(x_973, 0);
lean_dec(x_976);
x_977 = lean_box(0);
lean_ctor_set(x_973, 0, x_977);
return x_973;
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_978 = lean_ctor_get(x_973, 1);
lean_inc(x_978);
lean_dec(x_973);
x_979 = lean_box(0);
x_980 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_978);
return x_980;
}
}
else
{
uint8_t x_981; 
x_981 = !lean_is_exclusive(x_973);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; uint8_t x_988; 
x_982 = lean_ctor_get(x_973, 1);
x_983 = lean_ctor_get(x_973, 0);
lean_dec(x_983);
x_984 = lean_ctor_get(x_974, 0);
lean_inc(x_984);
lean_dec(x_974);
x_985 = l_Lean_Compiler_LCNF_Decl_getArity(x_984);
x_986 = lean_unsigned_to_nat(0u);
x_987 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_986);
x_988 = lean_nat_dec_eq(x_985, x_987);
lean_dec(x_985);
if (x_988 == 0)
{
lean_object* x_989; 
lean_dec(x_987);
lean_dec(x_984);
lean_dec(x_972);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_989 = lean_box(0);
lean_ctor_set(x_973, 0, x_989);
return x_973;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
lean_free_object(x_973);
lean_inc(x_984);
x_990 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_984, x_972);
x_991 = lean_ctor_get(x_984, 3);
lean_inc(x_991);
lean_dec(x_984);
x_992 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_987);
x_993 = lean_mk_array(x_987, x_992);
x_994 = lean_unsigned_to_nat(1u);
x_995 = lean_nat_sub(x_987, x_994);
lean_dec(x_987);
x_996 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_993, x_995);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_997 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_991, x_990, x_996, x_10, x_4, x_5, x_6, x_7, x_8, x_982);
lean_dec(x_991);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_998, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_999);
return x_1000;
}
else
{
uint8_t x_1001; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1001 = !lean_is_exclusive(x_997);
if (x_1001 == 0)
{
return x_997;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_997, 0);
x_1003 = lean_ctor_get(x_997, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_997);
x_1004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
return x_1004;
}
}
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
x_1005 = lean_ctor_get(x_973, 1);
lean_inc(x_1005);
lean_dec(x_973);
x_1006 = lean_ctor_get(x_974, 0);
lean_inc(x_1006);
lean_dec(x_974);
x_1007 = l_Lean_Compiler_LCNF_Decl_getArity(x_1006);
x_1008 = lean_unsigned_to_nat(0u);
x_1009 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_12, x_1008);
x_1010 = lean_nat_dec_eq(x_1007, x_1009);
lean_dec(x_1007);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_972);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1011 = lean_box(0);
x_1012 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_1005);
return x_1012;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_inc(x_1006);
x_1013 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_1006, x_972);
x_1014 = lean_ctor_get(x_1006, 3);
lean_inc(x_1014);
lean_dec(x_1006);
x_1015 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_1009);
x_1016 = lean_mk_array(x_1009, x_1015);
x_1017 = lean_unsigned_to_nat(1u);
x_1018 = lean_nat_sub(x_1009, x_1017);
lean_dec(x_1009);
x_1019 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_1016, x_1018);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1020 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1014, x_1013, x_1019, x_10, x_4, x_5, x_6, x_7, x_8, x_1005);
lean_dec(x_1014);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec(x_1020);
x_1023 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_1021, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1022);
return x_1023;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1024 = lean_ctor_get(x_1020, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1020, 1);
lean_inc(x_1025);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 x_1026 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1024);
lean_ctor_set(x_1027, 1, x_1025);
return x_1027;
}
}
}
}
}
else
{
uint8_t x_1028; 
lean_dec(x_972);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1028 = !lean_is_exclusive(x_973);
if (x_1028 == 0)
{
return x_973;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_973, 0);
x_1030 = lean_ctor_get(x_973, 1);
lean_inc(x_1030);
lean_inc(x_1029);
lean_dec(x_973);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
}
else
{
lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_970);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1032 = lean_box(0);
if (lean_is_scalar(x_967)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_967;
}
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_966);
return x_1033;
}
}
else
{
lean_object* x_1034; lean_object* x_1035; 
lean_dec(x_12);
x_1034 = lean_ctor_get(x_969, 0);
lean_inc(x_1034);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 x_1035 = x_969;
} else {
 lean_dec_ref(x_969);
 x_1035 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_967);
x_1036 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_1037 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_1036, x_3, x_4, x_5, x_6, x_7, x_8, x_966);
return x_1037;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; uint8_t x_1045; uint8_t x_1046; lean_object* x_1047; 
x_1038 = lean_ctor_get(x_1034, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1034, 1);
lean_inc(x_1039);
lean_dec(x_1034);
x_1040 = lean_ctor_get(x_2, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_2, 1);
lean_inc(x_1041);
lean_dec(x_2);
x_1042 = lean_ctor_get(x_1038, 3);
lean_inc(x_1042);
lean_dec(x_1038);
x_1043 = lean_nat_add(x_1042, x_1040);
lean_dec(x_1040);
lean_dec(x_1042);
x_1044 = lean_array_get_size(x_1039);
x_1045 = lean_nat_dec_lt(x_1043, x_1044);
lean_dec(x_1044);
x_1046 = l_List_isEmpty___rarg(x_1041);
if (x_1045 == 0)
{
lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1043);
lean_dec(x_1039);
x_1055 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_1056 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_1055);
x_1047 = x_1056;
goto block_1054;
}
else
{
lean_object* x_1057; 
x_1057 = lean_array_fget(x_1039, x_1043);
lean_dec(x_1043);
lean_dec(x_1039);
x_1047 = x_1057;
goto block_1054;
}
block_1054:
{
if (x_1046 == 0)
{
lean_dec(x_1035);
lean_dec(x_967);
x_1 = x_1047;
x_2 = x_1041;
x_9 = x_966;
goto _start;
}
else
{
lean_dec(x_1041);
if (lean_obj_tag(x_1047) == 1)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1049 = lean_ctor_get(x_1047, 0);
lean_inc(x_1049);
lean_dec(x_1047);
if (lean_is_scalar(x_1035)) {
 x_1050 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1050 = x_1035;
}
lean_ctor_set(x_1050, 0, x_1049);
if (lean_is_scalar(x_967)) {
 x_1051 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1051 = x_967;
}
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_966);
return x_1051;
}
else
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1047);
lean_dec(x_1035);
lean_dec(x_967);
x_1052 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_1053 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_1052, x_3, x_4, x_5, x_6, x_7, x_8, x_966);
return x_1053;
}
}
}
}
}
}
default: 
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1058 = lean_ctor_get(x_11, 1);
lean_inc(x_1058);
lean_dec(x_11);
x_1059 = lean_ctor_get(x_12, 1);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_12, 2);
lean_inc(x_1060);
lean_dec(x_12);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_2);
x_1 = x_1060;
x_2 = x_1061;
x_9 = x_1058;
goto _start;
}
}
}
else
{
uint8_t x_1063; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1063 = !lean_is_exclusive(x_11);
if (x_1063 == 0)
{
return x_11;
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1064 = lean_ctor_get(x_11, 0);
x_1065 = lean_ctor_get(x_11, 1);
lean_inc(x_1065);
lean_inc(x_1064);
lean_dec(x_11);
x_1066 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1066, 0, x_1064);
lean_ctor_set(x_1066, 1, x_1065);
return x_1066;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
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
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
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
else
{
uint8_t x_65; 
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
case 4:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_7);
return x_70;
}
case 5:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_7);
return x_72;
}
case 6:
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_7);
return x_74;
}
default: 
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_dec(x_1);
x_1 = x_75;
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
x_12 = lean_ctor_get(x_2, 0);
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
x_20 = lean_ctor_get(x_2, 0);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_array_uget(x_15, x_4);
x_27 = l_Lean_Compiler_LCNF_AltCore_getCode(x_16);
lean_dec(x_16);
x_28 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(x_27, x_6, x_7, x_8, x_9, x_10, x_11);
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
}
else
{
uint8_t x_37; 
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
lean_object* x_8; lean_object* x_9; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_73 = lean_array_get_size(x_8);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_77 = l_panic___at_Lean_Compiler_LCNF_CasesCore_extractAlt_x21___spec__2(x_76);
x_9 = x_77;
goto block_72;
}
else
{
lean_object* x_78; 
x_78 = lean_array_fget(x_8, x_74);
x_9 = x_78;
goto block_72;
}
block_72:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Compiler_LCNF_AltCore_getCode(x_9);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f_isCtorJmp_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
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
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
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
else
{
uint8_t x_60; 
lean_dec(x_20);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_20);
lean_dec(x_8);
x_64 = !lean_is_exclusive(x_21);
if (x_64 == 0)
{
return x_21;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_21, 0);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_21);
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
uint8_t x_68; 
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
return x_11;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_11, 0);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_11);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
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
x_3 = lean_unsigned_to_nat(730u);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Compiler_LCNF_eraseParams(x_31, x_8, x_9, x_10, x_11);
lean_dec(x_31);
x_34 = lean_unbox(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_LCNF_eraseFVarsAt(x_32, x_8, x_9, x_10, x_35);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_Compiler_LCNF_eraseParams(x_66, x_8, x_9, x_10, x_11);
lean_dec(x_66);
x_69 = lean_unbox(x_58);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_eraseFVarsAt(x_67, x_8, x_9, x_10, x_70);
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
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_Compiler_LCNF_Simp_findExpr(x_1, x_8, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
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
x_14 = lean_ctor_get(x_2, 1);
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
x_19 = lean_ctor_get(x_2, 1);
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
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_findCtor(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_constructorApp_x3f(x_17, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_8);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
uint8_t x_20; 
lean_free_object(x_13);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_22, 3);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_nat_add(x_27, x_8);
lean_dec(x_8);
lean_dec(x_27);
x_29 = lean_array_get_size(x_23);
x_30 = lean_nat_dec_lt(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_23);
x_31 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_32 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_31);
lean_ctor_set(x_18, 0, x_32);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_23, x_28);
lean_dec(x_28);
lean_dec(x_23);
lean_ctor_set(x_18, 0, x_33);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_22, 3);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_nat_add(x_35, x_8);
lean_dec(x_8);
lean_dec(x_35);
x_37 = lean_array_get_size(x_23);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_23);
x_39 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_40 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_39);
lean_ctor_set(x_18, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_array_fget(x_23, x_36);
lean_dec(x_36);
lean_dec(x_23);
lean_ctor_set(x_18, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_ctor_get(x_18, 0);
lean_inc(x_44);
lean_dec(x_18);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_16);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_45, 3);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_nat_add(x_50, x_8);
lean_dec(x_8);
lean_dec(x_50);
x_52 = lean_array_get_size(x_46);
x_53 = lean_nat_dec_lt(x_51, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_51);
lean_dec(x_46);
x_54 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_55 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_array_fget(x_46, x_51);
lean_dec(x_51);
lean_dec(x_46);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_49)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_49;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Expr_constructorApp_x3f(x_63, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_62);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_nat_add(x_74, x_8);
lean_dec(x_8);
lean_dec(x_74);
x_76 = lean_array_get_size(x_70);
x_77 = lean_nat_dec_lt(x_75, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_75);
lean_dec(x_70);
x_78 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_79 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_78);
if (lean_is_scalar(x_68)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_68;
}
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_73)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_73;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_72);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_array_fget(x_70, x_75);
lean_dec(x_75);
lean_dec(x_70);
if (lean_is_scalar(x_68)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_68;
}
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_73)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_73;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_72);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_10);
if (x_85 == 0)
{
return x_10;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_10, 0);
x_87 = lean_ctor_get(x_10, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_10);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_7);
return x_90;
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
lean_object* x_147; 
x_147 = lean_box(0);
x_9 = x_147;
x_10 = x_7;
goto block_146;
}
else
{
lean_object* x_148; 
x_148 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
x_9 = x_148;
x_10 = x_7;
goto block_146;
}
block_146:
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
uint8_t x_19; lean_object* x_20; 
x_19 = 1;
x_20 = l_Lean_Compiler_LCNF_Simp_findExpr(x_15, x_19, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
x_32 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_41 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_53 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_62 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_80 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_92 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
else
{
uint8_t x_99; 
lean_free_object(x_9);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_20);
if (x_99 == 0)
{
return x_20;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_20, 0);
x_101 = lean_ctor_get(x_20, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_20);
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
lean_object* x_103; uint8_t x_104; 
lean_dec(x_9);
x_103 = l_Lean_Expr_getAppFn(x_1);
x_104 = l_Lean_Expr_isFVar(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_103);
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_10);
return x_106;
}
else
{
uint8_t x_107; lean_object* x_108; 
x_107 = 1;
x_108 = l_Lean_Compiler_LCNF_Simp_findExpr(x_103, x_107, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = l_Lean_Expr_isApp(x_109);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Expr_isConst(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_109);
lean_dec(x_1);
x_114 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_111);
x_116 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_110);
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
x_119 = lean_unsigned_to_nat(0u);
x_120 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_119);
x_121 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_120);
x_122 = lean_mk_array(x_120, x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_sub(x_120, x_123);
lean_dec(x_120);
x_125 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_122, x_124);
x_126 = l_Lean_mkAppN(x_109, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
if (lean_is_scalar(x_118)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_118;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_117);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_111);
x_129 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_110);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_unsigned_to_nat(0u);
x_133 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_132);
x_134 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
lean_inc(x_133);
x_135 = lean_mk_array(x_133, x_134);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_sub(x_133, x_136);
lean_dec(x_133);
x_138 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_135, x_137);
x_139 = l_Lean_mkAppN(x_109, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_131)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_131;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_130);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_108, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_108, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_144 = x_108;
} else {
 lean_dec_ref(x_108);
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
x_8 = lean_ctor_get(x_2, 0);
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
x_34 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_44 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_58 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
x_82 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__1;
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
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
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
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_8, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_8, 0, x_33);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_36 = x_9;
} else {
 lean_dec_ref(x_9);
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
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = l_Lean_Compiler_LCNF_eraseFVar(x_1, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_8 = lean_ctor_get(x_2, 0);
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
lean_dec(x_1);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = l_Lean_Expr_fvar___override(x_68);
lean_inc(x_67);
x_70 = l_Lean_Compiler_LCNF_Simp_addSubst(x_67, x_69, x_2, x_3, x_4, x_5, x_6, x_66);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_67, x_2, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_1);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = l_Lean_Expr_fvar___override(x_112);
lean_inc(x_111);
x_114 = l_Lean_Compiler_LCNF_Simp_addSubst(x_111, x_113, x_2, x_3, x_4, x_5, x_6, x_110);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_111, x_2, x_3, x_4, x_5, x_6, x_115);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_1);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = l_Lean_Expr_fvar___override(x_159);
lean_inc(x_158);
x_161 = l_Lean_Compiler_LCNF_Simp_addSubst(x_158, x_160, x_2, x_3, x_4, x_5, x_6, x_157);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_158, x_2, x_3, x_4, x_5, x_6, x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_1);
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
x_235 = l_Lean_Expr_fvar___override(x_234);
lean_inc(x_233);
x_236 = l_Lean_Compiler_LCNF_Simp_addSubst(x_233, x_235, x_2, x_3, x_4, x_5, x_6, x_232);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_233, x_2, x_3, x_4, x_5, x_6, x_237);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_55; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_inc(x_26);
x_27 = l_Lean_Compiler_LCNF_Simp_isUsed(x_26, x_6, x_7, x_8, x_9, x_10, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_28);
lean_dec(x_26);
x_56 = lean_box(0);
x_30 = x_56;
goto block_54;
}
else
{
uint8_t x_57; 
x_57 = lean_unbox(x_28);
lean_dec(x_28);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_26, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_24);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_24);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_26);
x_63 = lean_box(0);
x_30 = x_63;
goto block_54;
}
}
block_54:
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_inc(x_4);
x_31 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_35 = lean_ptr_addr(x_24);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
x_38 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_39 = lean_ptr_addr(x_4);
x_40 = lean_usize_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_31, 0, x_41);
return x_31;
}
else
{
lean_dec(x_24);
lean_dec(x_4);
lean_ctor_set(x_31, 0, x_3);
return x_31;
}
}
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_44 = lean_ptr_addr(x_24);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_24);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_49 = lean_ptr_addr(x_4);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_24);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_24);
lean_dec(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_23);
if (x_64 == 0)
{
return x_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_23, 0);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_23);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_21, 0);
lean_inc(x_68);
lean_dec(x_21);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_dec(x_20);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
lean_dec(x_4);
x_73 = l_Lean_Expr_fvar___override(x_71);
lean_inc(x_72);
x_74 = l_Lean_Compiler_LCNF_Simp_addSubst(x_72, x_73, x_6, x_7, x_8, x_9, x_10, x_69);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_72, x_6, x_7, x_8, x_9, x_10, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_70, x_79, x_6, x_7, x_8, x_9, x_10, x_80);
lean_dec(x_70);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
return x_78;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 0);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_78);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_20);
if (x_86 == 0)
{
return x_20;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_20, 0);
x_88 = lean_ctor_get(x_20, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_20);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_dec(x_17);
x_91 = lean_ctor_get(x_18, 0);
lean_inc(x_91);
lean_dec(x_18);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
lean_dec(x_4);
x_93 = 1;
x_94 = l_Lean_Compiler_LCNF_eraseFVar(x_92, x_93, x_8, x_9, x_10, x_90);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Compiler_LCNF_Simp_simp(x_91, x_6, x_7, x_8, x_9, x_10, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
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
x_97 = !lean_is_exclusive(x_17);
if (x_97 == 0)
{
return x_17;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_17, 0);
x_99 = lean_ctor_get(x_17, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_17);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_4, 0);
lean_inc(x_101);
lean_dec(x_4);
lean_inc(x_101);
x_102 = l_Lean_Compiler_LCNF_Simp_addSubst(x_101, x_15, x_6, x_7, x_8, x_9, x_10, x_14);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_101, x_6, x_7, x_8, x_9, x_10, x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_ctor_get(x_12, 1);
lean_inc(x_107);
lean_dec(x_12);
x_108 = lean_ctor_get(x_13, 0);
lean_inc(x_108);
lean_dec(x_13);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_1);
x_110 = l_Lean_Compiler_LCNF_Simp_simp(x_109, x_6, x_7, x_8, x_9, x_10, x_107);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_12);
if (x_111 == 0)
{
return x_12;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_12, 0);
x_113 = lean_ctor_get(x_12, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_12);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_7, x_8, x_9, x_10, x_11, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_16, x_7, x_8, x_9, x_10, x_11, x_20);
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
lean_dec(x_16);
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
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Simp_isUsed(x_16, x_7, x_8, x_9, x_10, x_11, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Compiler_LCNF_Simp_eraseLocalDecl(x_16, x_7, x_8, x_9, x_10, x_11, x_20);
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
lean_dec(x_16);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
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
else
{
uint8_t x_54; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_dec(x_34);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_61, x_2, x_3, x_4, x_5, x_6, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
lean_inc(x_1);
lean_inc(x_59);
x_66 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 12, 4);
lean_closure_set(x_66, 0, x_60);
lean_closure_set(x_66, 1, x_59);
lean_closure_set(x_66, 2, x_1);
lean_closure_set(x_66, 3, x_63);
x_67 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
x_69 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_66, x_59, x_68, x_2, x_3, x_4, x_5, x_6, x_65);
return x_69;
}
else
{
lean_object* x_70; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_59, x_4, x_5, x_6, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_66, x_71, x_73, x_2, x_3, x_4, x_5, x_6, x_72);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_dec(x_62);
x_80 = lean_st_ref_get(x_6, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_3, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_59);
x_86 = l_Lean_Compiler_LCNF_normFunDeclImp(x_59, x_85, x_4, x_5, x_6, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
x_90 = lean_unbox(x_63);
lean_dec(x_63);
x_91 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_60, x_59, x_1, x_90, x_87, x_89, x_2, x_3, x_4, x_5, x_6, x_88);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_34, 1);
lean_inc(x_96);
lean_dec(x_34);
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_99, x_2, x_3, x_4, x_5, x_6, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
lean_inc(x_1);
lean_inc(x_97);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 12, 4);
lean_closure_set(x_104, 0, x_98);
lean_closure_set(x_104, 1, x_97);
lean_closure_set(x_104, 2, x_1);
lean_closure_set(x_104, 3, x_101);
x_105 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_104, x_97, x_106, x_2, x_3, x_4, x_5, x_6, x_103);
return x_107;
}
else
{
lean_object* x_108; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_108 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_97, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
x_112 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_104, x_109, x_111, x_2, x_3, x_4, x_5, x_6, x_110);
return x_112;
}
else
{
uint8_t x_113; 
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
return x_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_108);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_100, 1);
lean_inc(x_117);
lean_dec(x_100);
x_118 = lean_st_ref_get(x_6, x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_st_ref_get(x_3, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_97);
x_124 = l_Lean_Compiler_LCNF_normFunDeclImp(x_97, x_123, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_box(0);
x_128 = lean_unbox(x_101);
lean_dec(x_101);
x_129 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_98, x_97, x_1, x_128, x_125, x_127, x_2, x_3, x_4, x_5, x_6, x_126);
return x_129;
}
else
{
uint8_t x_130; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 3:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_ctor_get(x_34, 1);
lean_inc(x_134);
lean_dec(x_34);
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
x_137 = lean_st_ref_get(x_6, x_134);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_st_ref_get(x_3, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_135);
x_143 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_142, x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_136);
x_144 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_136, x_2, x_3, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_167; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_145);
lean_inc(x_143);
x_167 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_143, x_145, x_2, x_3, x_4, x_5, x_6, x_146);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_143);
x_170 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_143, x_2, x_3, x_4, x_5, x_6, x_169);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_array_get_size(x_145);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_dec_lt(x_173, x_172);
if (x_174 == 0)
{
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = x_171;
goto block_166;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_172, x_172);
if (x_175 == 0)
{
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = x_171;
goto block_166;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = 0;
x_177 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_178 = lean_box(0);
x_179 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_145, x_176, x_177, x_178, x_2, x_3, x_4, x_5, x_6, x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_148 = x_180;
goto block_166;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_1);
x_181 = lean_ctor_get(x_167, 1);
lean_inc(x_181);
lean_dec(x_167);
x_182 = lean_ctor_get(x_168, 0);
lean_inc(x_182);
lean_dec(x_168);
x_1 = x_182;
x_7 = x_181;
goto _start;
}
}
else
{
uint8_t x_184; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_167);
if (x_184 == 0)
{
return x_167;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_167, 0);
x_186 = lean_ctor_get(x_167, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_167);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
block_166:
{
uint8_t x_149; 
x_149 = lean_name_eq(x_135, x_143);
lean_dec(x_135);
if (x_149 == 0)
{
uint8_t x_150; 
lean_dec(x_136);
x_150 = !lean_is_exclusive(x_1);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_1, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_1, 0);
lean_dec(x_152);
lean_ctor_set(x_1, 1, x_145);
lean_ctor_set(x_1, 0, x_143);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_147;
}
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_148);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_1);
x_154 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_145);
if (lean_is_scalar(x_147)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_147;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_148);
return x_155;
}
}
else
{
size_t x_156; size_t x_157; uint8_t x_158; 
x_156 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_157 = lean_ptr_addr(x_145);
x_158 = lean_usize_dec_eq(x_156, x_157);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_1);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_1, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_1, 0);
lean_dec(x_161);
lean_ctor_set(x_1, 1, x_145);
lean_ctor_set(x_1, 0, x_143);
if (lean_is_scalar(x_147)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_147;
}
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_148);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_163 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_163, 0, x_143);
lean_ctor_set(x_163, 1, x_145);
if (lean_is_scalar(x_147)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_147;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_148);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec(x_145);
lean_dec(x_143);
if (lean_is_scalar(x_147)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_147;
}
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_148);
return x_165;
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_144);
if (x_188 == 0)
{
return x_144;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_144, 0);
x_190 = lean_ctor_get(x_144, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_144);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
case 4:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_34, 1);
lean_inc(x_192);
lean_dec(x_34);
x_193 = lean_ctor_get(x_1, 0);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_193);
x_194 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_193, x_2, x_3, x_4, x_5, x_6, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 3);
lean_inc(x_200);
lean_inc(x_199);
x_201 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 8, 1);
lean_closure_set(x_201, 0, x_199);
x_202 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_203 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_203, 0, x_202);
lean_closure_set(x_203, 1, x_201);
lean_inc(x_1);
lean_inc(x_199);
lean_inc(x_193);
x_204 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed), 10, 3);
lean_closure_set(x_204, 0, x_193);
lean_closure_set(x_204, 1, x_199);
lean_closure_set(x_204, 2, x_1);
x_205 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_205, 0, x_203);
lean_closure_set(x_205, 1, x_204);
lean_inc(x_193);
x_206 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(x_193, x_2, x_3, x_4, x_5, x_6, x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_207 = x_193;
} else {
 lean_dec_ref(x_193);
 x_207 = lean_box(0);
}
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_205);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_st_ref_get(x_6, x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_st_ref_get(x_3, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_199);
x_216 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_215, x_199);
x_217 = lean_st_ref_get(x_6, x_214);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_st_ref_get(x_3, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_198);
x_223 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_222, x_198);
lean_inc(x_216);
x_224 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_216, x_2, x_3, x_4, x_5, x_6, x_221);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
lean_inc(x_216);
x_226 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__9), 8, 1);
lean_closure_set(x_226, 0, x_216);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_200);
x_227 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_200, x_226, x_2, x_3, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
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
x_231 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(x_228, x_2, x_3, x_4, x_5, x_6, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_266; lean_object* x_267; uint8_t x_278; 
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
x_266 = lean_array_get_size(x_232);
x_278 = lean_nat_dec_eq(x_266, x_32);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_266);
lean_dec(x_230);
x_279 = lean_box(0);
x_235 = x_279;
goto block_265;
}
else
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_unsigned_to_nat(0u);
x_281 = lean_nat_dec_lt(x_280, x_266);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_283 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
lean_dec(x_283);
lean_dec(x_266);
lean_dec(x_230);
x_284 = lean_box(0);
x_235 = x_284;
goto block_265;
}
else
{
lean_object* x_285; 
lean_dec(x_283);
lean_dec(x_234);
lean_dec(x_223);
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_285 = lean_box(0);
x_267 = x_285;
goto block_277;
}
}
else
{
lean_object* x_286; 
x_286 = lean_array_fget(x_232, x_280);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
lean_dec(x_286);
lean_dec(x_266);
lean_dec(x_230);
x_287 = lean_box(0);
x_235 = x_287;
goto block_265;
}
else
{
lean_object* x_288; 
lean_dec(x_286);
lean_dec(x_234);
lean_dec(x_223);
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_288 = lean_box(0);
x_267 = x_288;
goto block_277;
}
}
}
block_265:
{
size_t x_236; size_t x_237; uint8_t x_238; 
lean_dec(x_235);
x_236 = lean_ptr_addr(x_200);
lean_dec(x_200);
x_237 = lean_ptr_addr(x_232);
x_238 = lean_usize_dec_eq(x_236, x_237);
if (x_238 == 0)
{
uint8_t x_239; 
lean_dec(x_199);
lean_dec(x_198);
x_239 = !lean_is_exclusive(x_1);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_1, 0);
lean_dec(x_240);
if (lean_is_scalar(x_207)) {
 x_241 = lean_alloc_ctor(0, 4, 0);
} else {
 x_241 = x_207;
}
lean_ctor_set(x_241, 0, x_197);
lean_ctor_set(x_241, 1, x_223);
lean_ctor_set(x_241, 2, x_216);
lean_ctor_set(x_241, 3, x_232);
lean_ctor_set(x_1, 0, x_241);
if (lean_is_scalar(x_234)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_234;
}
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set(x_242, 1, x_233);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_1);
if (lean_is_scalar(x_207)) {
 x_243 = lean_alloc_ctor(0, 4, 0);
} else {
 x_243 = x_207;
}
lean_ctor_set(x_243, 0, x_197);
lean_ctor_set(x_243, 1, x_223);
lean_ctor_set(x_243, 2, x_216);
lean_ctor_set(x_243, 3, x_232);
x_244 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_244, 0, x_243);
if (lean_is_scalar(x_234)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_234;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_233);
return x_245;
}
}
else
{
size_t x_246; size_t x_247; uint8_t x_248; 
x_246 = lean_ptr_addr(x_198);
lean_dec(x_198);
x_247 = lean_ptr_addr(x_223);
x_248 = lean_usize_dec_eq(x_246, x_247);
if (x_248 == 0)
{
uint8_t x_249; 
lean_dec(x_199);
x_249 = !lean_is_exclusive(x_1);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_1, 0);
lean_dec(x_250);
if (lean_is_scalar(x_207)) {
 x_251 = lean_alloc_ctor(0, 4, 0);
} else {
 x_251 = x_207;
}
lean_ctor_set(x_251, 0, x_197);
lean_ctor_set(x_251, 1, x_223);
lean_ctor_set(x_251, 2, x_216);
lean_ctor_set(x_251, 3, x_232);
lean_ctor_set(x_1, 0, x_251);
if (lean_is_scalar(x_234)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_234;
}
lean_ctor_set(x_252, 0, x_1);
lean_ctor_set(x_252, 1, x_233);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_1);
if (lean_is_scalar(x_207)) {
 x_253 = lean_alloc_ctor(0, 4, 0);
} else {
 x_253 = x_207;
}
lean_ctor_set(x_253, 0, x_197);
lean_ctor_set(x_253, 1, x_223);
lean_ctor_set(x_253, 2, x_216);
lean_ctor_set(x_253, 3, x_232);
x_254 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_234)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_234;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_233);
return x_255;
}
}
else
{
uint8_t x_256; 
x_256 = lean_name_eq(x_199, x_216);
lean_dec(x_199);
if (x_256 == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_1);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_1, 0);
lean_dec(x_258);
if (lean_is_scalar(x_207)) {
 x_259 = lean_alloc_ctor(0, 4, 0);
} else {
 x_259 = x_207;
}
lean_ctor_set(x_259, 0, x_197);
lean_ctor_set(x_259, 1, x_223);
lean_ctor_set(x_259, 2, x_216);
lean_ctor_set(x_259, 3, x_232);
lean_ctor_set(x_1, 0, x_259);
if (lean_is_scalar(x_234)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_234;
}
lean_ctor_set(x_260, 0, x_1);
lean_ctor_set(x_260, 1, x_233);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_1);
if (lean_is_scalar(x_207)) {
 x_261 = lean_alloc_ctor(0, 4, 0);
} else {
 x_261 = x_207;
}
lean_ctor_set(x_261, 0, x_197);
lean_ctor_set(x_261, 1, x_223);
lean_ctor_set(x_261, 2, x_216);
lean_ctor_set(x_261, 3, x_232);
x_262 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_262, 0, x_261);
if (lean_is_scalar(x_234)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_234;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_233);
return x_263;
}
}
else
{
lean_object* x_264; 
lean_dec(x_232);
lean_dec(x_223);
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_197);
if (lean_is_scalar(x_234)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_234;
}
lean_ctor_set(x_264, 0, x_1);
lean_ctor_set(x_264, 1, x_233);
return x_264;
}
}
}
}
block_277:
{
lean_object* x_268; uint8_t x_269; 
lean_dec(x_267);
x_268 = lean_unsigned_to_nat(0u);
x_269 = lean_nat_dec_lt(x_268, x_266);
lean_dec(x_266);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_232);
x_270 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_271 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_270);
x_272 = l_Lean_Compiler_LCNF_AltCore_getCode(x_271);
lean_dec(x_271);
if (lean_is_scalar(x_230)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_230;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_233);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_array_fget(x_232, x_268);
lean_dec(x_232);
x_275 = l_Lean_Compiler_LCNF_AltCore_getCode(x_274);
lean_dec(x_274);
if (lean_is_scalar(x_230)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_230;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_233);
return x_276;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_230);
lean_dec(x_223);
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_231);
if (x_289 == 0)
{
return x_231;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_231, 0);
x_291 = lean_ctor_get(x_231, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_231);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_223);
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_227);
if (x_293 == 0)
{
return x_227;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_227, 0);
x_295 = lean_ctor_get(x_227, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_227);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_207);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_297 = lean_ctor_get(x_206, 1);
lean_inc(x_297);
lean_dec(x_206);
x_298 = lean_ctor_get(x_208, 0);
lean_inc(x_298);
lean_dec(x_208);
x_299 = l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(x_298, x_205, x_2, x_3, x_4, x_5, x_6, x_297);
return x_299;
}
}
else
{
uint8_t x_300; 
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
return x_206;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_206, 0);
x_302 = lean_ctor_get(x_206, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_206);
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
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_194);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_194, 0);
lean_dec(x_305);
x_306 = lean_ctor_get(x_195, 0);
lean_inc(x_306);
lean_dec(x_195);
lean_ctor_set(x_194, 0, x_306);
return x_194;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_194, 1);
lean_inc(x_307);
lean_dec(x_194);
x_308 = lean_ctor_get(x_195, 0);
lean_inc(x_308);
lean_dec(x_195);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_193);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_194);
if (x_310 == 0)
{
return x_194;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_194, 0);
x_312 = lean_ctor_get(x_194, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_194);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
case 5:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_314 = lean_ctor_get(x_34, 1);
lean_inc(x_314);
lean_dec(x_34);
x_315 = lean_ctor_get(x_1, 0);
lean_inc(x_315);
x_316 = lean_st_ref_get(x_6, x_314);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_st_ref_get(x_3, x_317);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_315);
x_322 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_321, x_315);
lean_inc(x_322);
x_323 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_322, x_2, x_3, x_4, x_5, x_6, x_320);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; 
x_325 = lean_ctor_get(x_323, 0);
lean_dec(x_325);
x_326 = lean_name_eq(x_315, x_322);
lean_dec(x_315);
if (x_326 == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_1);
if (x_327 == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_1, 0);
lean_dec(x_328);
lean_ctor_set(x_1, 0, x_322);
lean_ctor_set(x_323, 0, x_1);
return x_323;
}
else
{
lean_object* x_329; 
lean_dec(x_1);
x_329 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_323, 0, x_329);
return x_323;
}
}
else
{
lean_dec(x_322);
lean_ctor_set(x_323, 0, x_1);
return x_323;
}
}
else
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_323, 1);
lean_inc(x_330);
lean_dec(x_323);
x_331 = lean_name_eq(x_315, x_322);
lean_dec(x_315);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_332 = x_1;
} else {
 lean_dec_ref(x_1);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(5, 1, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_322);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_330);
return x_334;
}
else
{
lean_object* x_335; 
lean_dec(x_322);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_1);
lean_ctor_set(x_335, 1, x_330);
return x_335;
}
}
}
default: 
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_336 = lean_ctor_get(x_34, 1);
lean_inc(x_336);
lean_dec(x_34);
x_337 = lean_ctor_get(x_1, 0);
lean_inc(x_337);
x_338 = lean_st_ref_get(x_6, x_336);
lean_dec(x_6);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_st_ref_get(x_3, x_339);
lean_dec(x_3);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; size_t x_345; size_t x_346; uint8_t x_347; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec(x_342);
lean_inc(x_337);
x_344 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_343, x_337);
x_345 = lean_ptr_addr(x_337);
lean_dec(x_337);
x_346 = lean_ptr_addr(x_344);
x_347 = lean_usize_dec_eq(x_345, x_346);
if (x_347 == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_1);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_1, 0);
lean_dec(x_349);
lean_ctor_set(x_1, 0, x_344);
lean_ctor_set(x_340, 0, x_1);
return x_340;
}
else
{
lean_object* x_350; 
lean_dec(x_1);
x_350 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_340, 0, x_350);
return x_340;
}
}
else
{
lean_dec(x_344);
lean_ctor_set(x_340, 0, x_1);
return x_340;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; size_t x_355; size_t x_356; uint8_t x_357; 
x_351 = lean_ctor_get(x_340, 0);
x_352 = lean_ctor_get(x_340, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_340);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
lean_inc(x_337);
x_354 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_353, x_337);
x_355 = lean_ptr_addr(x_337);
lean_dec(x_337);
x_356 = lean_ptr_addr(x_354);
x_357 = lean_usize_dec_eq(x_355, x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_358 = x_1;
} else {
 lean_dec_ref(x_1);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(6, 1, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_354);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_352);
return x_360;
}
else
{
lean_object* x_361; 
lean_dec(x_354);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_1);
lean_ctor_set(x_361, 1, x_352);
return x_361;
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_5);
x_362 = lean_unsigned_to_nat(1u);
x_363 = lean_nat_add(x_11, x_362);
lean_dec(x_11);
x_364 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_364, 0, x_8);
lean_ctor_set(x_364, 1, x_9);
lean_ctor_set(x_364, 2, x_10);
lean_ctor_set(x_364, 3, x_363);
lean_ctor_set(x_364, 4, x_12);
lean_ctor_set(x_364, 5, x_13);
lean_ctor_set(x_364, 6, x_14);
lean_ctor_set(x_364, 7, x_15);
lean_ctor_set(x_364, 8, x_16);
lean_ctor_set(x_364, 9, x_17);
lean_ctor_set(x_364, 10, x_18);
x_365 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_364, x_6, x_7);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec(x_365);
x_367 = lean_ctor_get(x_1, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_1, 1);
lean_inc(x_368);
lean_inc(x_367);
x_369 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_367, x_2, x_3, x_4, x_364, x_6, x_366);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_ctor_get(x_370, 3);
lean_inc(x_372);
x_373 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_372, x_2, x_3, x_4, x_364, x_6, x_371);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_box(0);
x_377 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_368, x_367, x_1, x_370, x_376, x_2, x_3, x_4, x_364, x_6, x_375);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_373, 1);
lean_inc(x_378);
lean_dec(x_373);
x_379 = lean_ctor_get(x_374, 0);
lean_inc(x_379);
lean_dec(x_374);
x_380 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_370, x_379, x_4, x_364, x_6, x_378);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_box(0);
x_384 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_368, x_367, x_1, x_381, x_383, x_2, x_3, x_4, x_364, x_6, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_370);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_387 = x_373;
} else {
 lean_dec_ref(x_373);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
case 1:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_389 = lean_ctor_get(x_365, 1);
lean_inc(x_389);
lean_dec(x_365);
x_390 = lean_ctor_get(x_1, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_1, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 0);
lean_inc(x_392);
x_393 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_392, x_2, x_3, x_4, x_364, x_6, x_389);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_unbox(x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
lean_dec(x_393);
lean_inc(x_1);
lean_inc(x_390);
x_397 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 12, 4);
lean_closure_set(x_397, 0, x_391);
lean_closure_set(x_397, 1, x_390);
lean_closure_set(x_397, 2, x_1);
lean_closure_set(x_397, 3, x_394);
x_398 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_box(0);
x_400 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_397, x_390, x_399, x_2, x_3, x_4, x_364, x_6, x_396);
return x_400;
}
else
{
lean_object* x_401; 
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
x_401 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_390, x_4, x_364, x_6, x_396);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_box(0);
x_405 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_397, x_402, x_404, x_2, x_3, x_4, x_364, x_6, x_403);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_397);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_406 = lean_ctor_get(x_401, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_401, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_408 = x_401;
} else {
 lean_dec_ref(x_401);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_410 = lean_ctor_get(x_393, 1);
lean_inc(x_410);
lean_dec(x_393);
x_411 = lean_st_ref_get(x_6, x_410);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
lean_dec(x_411);
x_413 = lean_st_ref_get(x_3, x_412);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec(x_414);
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_390);
x_417 = l_Lean_Compiler_LCNF_normFunDeclImp(x_390, x_416, x_4, x_364, x_6, x_415);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_box(0);
x_421 = lean_unbox(x_394);
lean_dec(x_394);
x_422 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_391, x_390, x_1, x_421, x_418, x_420, x_2, x_3, x_4, x_364, x_6, x_419);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_394);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_423 = lean_ctor_get(x_417, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_417, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_425 = x_417;
} else {
 lean_dec_ref(x_417);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
}
case 2:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_427 = lean_ctor_get(x_365, 1);
lean_inc(x_427);
lean_dec(x_365);
x_428 = lean_ctor_get(x_1, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_1, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_430, x_2, x_3, x_4, x_364, x_6, x_427);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_unbox(x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; uint8_t x_436; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
lean_inc(x_1);
lean_inc(x_428);
x_435 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 12, 4);
lean_closure_set(x_435, 0, x_429);
lean_closure_set(x_435, 1, x_428);
lean_closure_set(x_435, 2, x_1);
lean_closure_set(x_435, 3, x_432);
x_436 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_box(0);
x_438 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_435, x_428, x_437, x_2, x_3, x_4, x_364, x_6, x_434);
return x_438;
}
else
{
lean_object* x_439; 
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
x_439 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_428, x_4, x_364, x_6, x_434);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_box(0);
x_443 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_435, x_440, x_442, x_2, x_3, x_4, x_364, x_6, x_441);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_435);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_444 = lean_ctor_get(x_439, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_439, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_446 = x_439;
} else {
 lean_dec_ref(x_439);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
return x_447;
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_448 = lean_ctor_get(x_431, 1);
lean_inc(x_448);
lean_dec(x_431);
x_449 = lean_st_ref_get(x_6, x_448);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = lean_st_ref_get(x_3, x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
lean_dec(x_452);
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_428);
x_455 = l_Lean_Compiler_LCNF_normFunDeclImp(x_428, x_454, x_4, x_364, x_6, x_453);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_box(0);
x_459 = lean_unbox(x_432);
lean_dec(x_432);
x_460 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_429, x_428, x_1, x_459, x_456, x_458, x_2, x_3, x_4, x_364, x_6, x_457);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_432);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = lean_ctor_get(x_455, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_455, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_463 = x_455;
} else {
 lean_dec_ref(x_455);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
}
}
case 3:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_465 = lean_ctor_get(x_365, 1);
lean_inc(x_465);
lean_dec(x_365);
x_466 = lean_ctor_get(x_1, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_1, 1);
lean_inc(x_467);
x_468 = lean_st_ref_get(x_6, x_465);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_470 = lean_st_ref_get(x_3, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
lean_dec(x_471);
lean_inc(x_466);
x_474 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_473, x_466);
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_467);
x_475 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_467, x_2, x_3, x_4, x_364, x_6, x_472);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_492; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_478 = x_475;
} else {
 lean_dec_ref(x_475);
 x_478 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_476);
lean_inc(x_474);
x_492 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_474, x_476, x_2, x_3, x_4, x_364, x_6, x_477);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
lean_inc(x_474);
x_495 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_474, x_2, x_3, x_4, x_364, x_6, x_494);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
lean_dec(x_495);
x_497 = lean_array_get_size(x_476);
x_498 = lean_unsigned_to_nat(0u);
x_499 = lean_nat_dec_lt(x_498, x_497);
if (x_499 == 0)
{
lean_dec(x_497);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_479 = x_496;
goto block_491;
}
else
{
uint8_t x_500; 
x_500 = lean_nat_dec_le(x_497, x_497);
if (x_500 == 0)
{
lean_dec(x_497);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_479 = x_496;
goto block_491;
}
else
{
size_t x_501; size_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_501 = 0;
x_502 = lean_usize_of_nat(x_497);
lean_dec(x_497);
x_503 = lean_box(0);
x_504 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedCode___spec__1(x_476, x_501, x_502, x_503, x_2, x_3, x_4, x_364, x_6, x_496);
lean_dec(x_6);
lean_dec(x_364);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
lean_dec(x_504);
x_479 = x_505;
goto block_491;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_1);
x_506 = lean_ctor_get(x_492, 1);
lean_inc(x_506);
lean_dec(x_492);
x_507 = lean_ctor_get(x_493, 0);
lean_inc(x_507);
lean_dec(x_493);
x_1 = x_507;
x_5 = x_364;
x_7 = x_506;
goto _start;
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_509 = lean_ctor_get(x_492, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_492, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_511 = x_492;
} else {
 lean_dec_ref(x_492);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_510);
return x_512;
}
block_491:
{
uint8_t x_480; 
x_480 = lean_name_eq(x_466, x_474);
lean_dec(x_466);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_467);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_481 = x_1;
} else {
 lean_dec_ref(x_1);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(3, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_476);
if (lean_is_scalar(x_478)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_478;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_479);
return x_483;
}
else
{
size_t x_484; size_t x_485; uint8_t x_486; 
x_484 = lean_ptr_addr(x_467);
lean_dec(x_467);
x_485 = lean_ptr_addr(x_476);
x_486 = lean_usize_dec_eq(x_484, x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_487 = x_1;
} else {
 lean_dec_ref(x_1);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(3, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_474);
lean_ctor_set(x_488, 1, x_476);
if (lean_is_scalar(x_478)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_478;
}
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_479);
return x_489;
}
else
{
lean_object* x_490; 
lean_dec(x_476);
lean_dec(x_474);
if (lean_is_scalar(x_478)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_478;
}
lean_ctor_set(x_490, 0, x_1);
lean_ctor_set(x_490, 1, x_479);
return x_490;
}
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_474);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_513 = lean_ctor_get(x_475, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_475, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_515 = x_475;
} else {
 lean_dec_ref(x_475);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
case 4:
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_365, 1);
lean_inc(x_517);
lean_dec(x_365);
x_518 = lean_ctor_get(x_1, 0);
lean_inc(x_518);
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_518);
x_519 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_518, x_2, x_3, x_4, x_364, x_6, x_517);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_ctor_get(x_518, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_518, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_518, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_518, 3);
lean_inc(x_525);
lean_inc(x_524);
x_526 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 8, 1);
lean_closure_set(x_526, 0, x_524);
x_527 = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
x_528 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_528, 0, x_527);
lean_closure_set(x_528, 1, x_526);
lean_inc(x_1);
lean_inc(x_524);
lean_inc(x_518);
x_529 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__10___boxed), 10, 3);
lean_closure_set(x_529, 0, x_518);
lean_closure_set(x_529, 1, x_524);
lean_closure_set(x_529, 2, x_1);
x_530 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpM___spec__1___rarg), 8, 2);
lean_closure_set(x_530, 0, x_528);
lean_closure_set(x_530, 1, x_529);
lean_inc(x_518);
x_531 = l_Lean_Compiler_LCNF_Simp_isCasesOnCases_x3f(x_518, x_2, x_3, x_4, x_364, x_6, x_521);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 lean_ctor_release(x_518, 3);
 x_532 = x_518;
} else {
 lean_dec_ref(x_518);
 x_532 = lean_box(0);
}
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_530);
x_534 = lean_ctor_get(x_531, 1);
lean_inc(x_534);
lean_dec(x_531);
x_535 = lean_st_ref_get(x_6, x_534);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = lean_st_ref_get(x_3, x_536);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_538, 0);
lean_inc(x_540);
lean_dec(x_538);
lean_inc(x_524);
x_541 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_540, x_524);
x_542 = lean_st_ref_get(x_6, x_539);
x_543 = lean_ctor_get(x_542, 1);
lean_inc(x_543);
lean_dec(x_542);
x_544 = lean_st_ref_get(x_3, x_543);
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
lean_dec(x_545);
lean_inc(x_523);
x_548 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_547, x_523);
lean_inc(x_541);
x_549 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_541, x_2, x_3, x_4, x_364, x_6, x_546);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
lean_dec(x_549);
lean_inc(x_541);
x_551 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__9), 8, 1);
lean_closure_set(x_551, 0, x_541);
lean_inc(x_6);
lean_inc(x_364);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_525);
x_552 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__6(x_525, x_551, x_2, x_3, x_4, x_364, x_6, x_550);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_555 = x_552;
} else {
 lean_dec_ref(x_552);
 x_555 = lean_box(0);
}
x_556 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Simp_addDefault(x_553, x_2, x_3, x_4, x_364, x_6, x_554);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_582; lean_object* x_583; uint8_t x_594; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
x_582 = lean_array_get_size(x_557);
x_594 = lean_nat_dec_eq(x_582, x_362);
if (x_594 == 0)
{
lean_object* x_595; 
lean_dec(x_582);
lean_dec(x_555);
x_595 = lean_box(0);
x_560 = x_595;
goto block_581;
}
else
{
lean_object* x_596; uint8_t x_597; 
x_596 = lean_unsigned_to_nat(0u);
x_597 = lean_nat_dec_lt(x_596, x_582);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; 
x_598 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_599 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_598);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; 
lean_dec(x_599);
lean_dec(x_582);
lean_dec(x_555);
x_600 = lean_box(0);
x_560 = x_600;
goto block_581;
}
else
{
lean_object* x_601; 
lean_dec(x_599);
lean_dec(x_559);
lean_dec(x_548);
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_601 = lean_box(0);
x_583 = x_601;
goto block_593;
}
}
else
{
lean_object* x_602; 
x_602 = lean_array_fget(x_557, x_596);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; 
lean_dec(x_602);
lean_dec(x_582);
lean_dec(x_555);
x_603 = lean_box(0);
x_560 = x_603;
goto block_581;
}
else
{
lean_object* x_604; 
lean_dec(x_602);
lean_dec(x_559);
lean_dec(x_548);
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_604 = lean_box(0);
x_583 = x_604;
goto block_593;
}
}
}
block_581:
{
size_t x_561; size_t x_562; uint8_t x_563; 
lean_dec(x_560);
x_561 = lean_ptr_addr(x_525);
lean_dec(x_525);
x_562 = lean_ptr_addr(x_557);
x_563 = lean_usize_dec_eq(x_561, x_562);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_524);
lean_dec(x_523);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_564 = x_1;
} else {
 lean_dec_ref(x_1);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_565 = lean_alloc_ctor(0, 4, 0);
} else {
 x_565 = x_532;
}
lean_ctor_set(x_565, 0, x_522);
lean_ctor_set(x_565, 1, x_548);
lean_ctor_set(x_565, 2, x_541);
lean_ctor_set(x_565, 3, x_557);
if (lean_is_scalar(x_564)) {
 x_566 = lean_alloc_ctor(4, 1, 0);
} else {
 x_566 = x_564;
}
lean_ctor_set(x_566, 0, x_565);
if (lean_is_scalar(x_559)) {
 x_567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_567 = x_559;
}
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_558);
return x_567;
}
else
{
size_t x_568; size_t x_569; uint8_t x_570; 
x_568 = lean_ptr_addr(x_523);
lean_dec(x_523);
x_569 = lean_ptr_addr(x_548);
x_570 = lean_usize_dec_eq(x_568, x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_524);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_571 = x_1;
} else {
 lean_dec_ref(x_1);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_572 = lean_alloc_ctor(0, 4, 0);
} else {
 x_572 = x_532;
}
lean_ctor_set(x_572, 0, x_522);
lean_ctor_set(x_572, 1, x_548);
lean_ctor_set(x_572, 2, x_541);
lean_ctor_set(x_572, 3, x_557);
if (lean_is_scalar(x_571)) {
 x_573 = lean_alloc_ctor(4, 1, 0);
} else {
 x_573 = x_571;
}
lean_ctor_set(x_573, 0, x_572);
if (lean_is_scalar(x_559)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_559;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_558);
return x_574;
}
else
{
uint8_t x_575; 
x_575 = lean_name_eq(x_524, x_541);
lean_dec(x_524);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_576 = x_1;
} else {
 lean_dec_ref(x_1);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_577 = lean_alloc_ctor(0, 4, 0);
} else {
 x_577 = x_532;
}
lean_ctor_set(x_577, 0, x_522);
lean_ctor_set(x_577, 1, x_548);
lean_ctor_set(x_577, 2, x_541);
lean_ctor_set(x_577, 3, x_557);
if (lean_is_scalar(x_576)) {
 x_578 = lean_alloc_ctor(4, 1, 0);
} else {
 x_578 = x_576;
}
lean_ctor_set(x_578, 0, x_577);
if (lean_is_scalar(x_559)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_559;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_558);
return x_579;
}
else
{
lean_object* x_580; 
lean_dec(x_557);
lean_dec(x_548);
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_522);
if (lean_is_scalar(x_559)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_559;
}
lean_ctor_set(x_580, 0, x_1);
lean_ctor_set(x_580, 1, x_558);
return x_580;
}
}
}
}
block_593:
{
lean_object* x_584; uint8_t x_585; 
lean_dec(x_583);
x_584 = lean_unsigned_to_nat(0u);
x_585 = lean_nat_dec_lt(x_584, x_582);
lean_dec(x_582);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_557);
x_586 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__4;
x_587 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___spec__1(x_586);
x_588 = l_Lean_Compiler_LCNF_AltCore_getCode(x_587);
lean_dec(x_587);
if (lean_is_scalar(x_555)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_555;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_558);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_array_fget(x_557, x_584);
lean_dec(x_557);
x_591 = l_Lean_Compiler_LCNF_AltCore_getCode(x_590);
lean_dec(x_590);
if (lean_is_scalar(x_555)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_555;
}
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_558);
return x_592;
}
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_555);
lean_dec(x_548);
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_605 = lean_ctor_get(x_556, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_556, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_607 = x_556;
} else {
 lean_dec_ref(x_556);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
return x_608;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_548);
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_609 = lean_ctor_get(x_552, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_552, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_611 = x_552;
} else {
 lean_dec_ref(x_552);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_532);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_613 = lean_ctor_get(x_531, 1);
lean_inc(x_613);
lean_dec(x_531);
x_614 = lean_ctor_get(x_533, 0);
lean_inc(x_614);
lean_dec(x_533);
x_615 = l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(x_614, x_530, x_2, x_3, x_4, x_364, x_6, x_613);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_616 = lean_ctor_get(x_531, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_531, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_618 = x_531;
} else {
 lean_dec_ref(x_531);
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
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_518);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_620 = lean_ctor_get(x_519, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_621 = x_519;
} else {
 lean_dec_ref(x_519);
 x_621 = lean_box(0);
}
x_622 = lean_ctor_get(x_520, 0);
lean_inc(x_622);
lean_dec(x_520);
if (lean_is_scalar(x_621)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_621;
}
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_620);
return x_623;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_518);
lean_dec(x_364);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_624 = lean_ctor_get(x_519, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_519, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_626 = x_519;
} else {
 lean_dec_ref(x_519);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
case 5:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_628 = lean_ctor_get(x_365, 1);
lean_inc(x_628);
lean_dec(x_365);
x_629 = lean_ctor_get(x_1, 0);
lean_inc(x_629);
x_630 = lean_st_ref_get(x_6, x_628);
x_631 = lean_ctor_get(x_630, 1);
lean_inc(x_631);
lean_dec(x_630);
x_632 = lean_st_ref_get(x_3, x_631);
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_ctor_get(x_633, 0);
lean_inc(x_635);
lean_dec(x_633);
lean_inc(x_629);
x_636 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_635, x_629);
lean_inc(x_636);
x_637 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_636, x_2, x_3, x_4, x_364, x_6, x_634);
lean_dec(x_6);
lean_dec(x_364);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_639 = x_637;
} else {
 lean_dec_ref(x_637);
 x_639 = lean_box(0);
}
x_640 = lean_name_eq(x_629, x_636);
lean_dec(x_629);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_641 = x_1;
} else {
 lean_dec_ref(x_1);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(5, 1, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_636);
if (lean_is_scalar(x_639)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_639;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_638);
return x_643;
}
else
{
lean_object* x_644; 
lean_dec(x_636);
if (lean_is_scalar(x_639)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_639;
}
lean_ctor_set(x_644, 0, x_1);
lean_ctor_set(x_644, 1, x_638);
return x_644;
}
}
default: 
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; size_t x_655; size_t x_656; uint8_t x_657; 
lean_dec(x_364);
lean_dec(x_4);
lean_dec(x_2);
x_645 = lean_ctor_get(x_365, 1);
lean_inc(x_645);
lean_dec(x_365);
x_646 = lean_ctor_get(x_1, 0);
lean_inc(x_646);
x_647 = lean_st_ref_get(x_6, x_645);
lean_dec(x_6);
x_648 = lean_ctor_get(x_647, 1);
lean_inc(x_648);
lean_dec(x_647);
x_649 = lean_st_ref_get(x_3, x_648);
lean_dec(x_3);
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
x_653 = lean_ctor_get(x_650, 0);
lean_inc(x_653);
lean_dec(x_650);
lean_inc(x_646);
x_654 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_653, x_646);
x_655 = lean_ptr_addr(x_646);
lean_dec(x_646);
x_656 = lean_ptr_addr(x_654);
x_657 = lean_usize_dec_eq(x_655, x_656);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_658 = x_1;
} else {
 lean_dec_ref(x_1);
 x_658 = lean_box(0);
}
if (lean_is_scalar(x_658)) {
 x_659 = lean_alloc_ctor(6, 1, 0);
} else {
 x_659 = x_658;
}
lean_ctor_set(x_659, 0, x_654);
if (lean_is_scalar(x_652)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_652;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_651);
return x_660;
}
else
{
lean_object* x_661; 
lean_dec(x_654);
if (lean_is_scalar(x_652)) {
 x_661 = lean_alloc_ctor(0, 2, 0);
} else {
 x_661 = x_652;
}
lean_ctor_set(x_661, 0, x_1);
lean_ctor_set(x_661, 1, x_651);
return x_661;
}
}
}
}
}
else
{
lean_object* x_662; 
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
x_662 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_Simp_simp___spec__8(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_662;
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_uget(x_1, x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_20 = lean_ctor_get(x_4, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_14, x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_15, x_24);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_25);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = l_Lean_Compiler_LCNF_Simp_addSubst(x_26, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_10 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
lean_dec(x_4);
x_32 = lean_array_fget(x_14, x_15);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_15, x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_16);
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = l_Lean_Compiler_LCNF_Simp_addSubst(x_36, x_32, x_5, x_6, x_7, x_8, x_9, x_10);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 1;
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
x_4 = x_35;
x_10 = x_38;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_6, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_constructorApp_x3f(x_24, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
uint8_t x_27; 
lean_free_object(x_20);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Compiler_LCNF_eraseFVarsAt(x_36, x_4, x_5, x_6, x_23);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 2);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_29, 3);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_array_get_size(x_30);
x_45 = l_Array_toSubarray___rarg(x_30, x_43, x_44);
x_46 = lean_array_get_size(x_41);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_41, x_47, x_48, x_45, x_2, x_3, x_4, x_5, x_6, x_40);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Compiler_LCNF_Simp_simp(x_42, x_2, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_LCNF_eraseParams(x_41, x_4, x_5, x_6, x_53);
lean_dec(x_41);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_25, 0, x_52);
lean_ctor_set(x_54, 0, x_25);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_25, 0, x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_25);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_41);
lean_free_object(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_30);
lean_dec(x_29);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_ctor_get(x_34, 0);
lean_inc(x_64);
lean_dec(x_34);
x_65 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set(x_25, 0, x_67);
lean_ctor_set(x_65, 0, x_25);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set(x_25, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_25);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_25);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_25, 0);
lean_inc(x_75);
lean_dec(x_25);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_Compiler_LCNF_eraseFVarsAt(x_83, x_4, x_5, x_6, x_23);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 2);
lean_inc(x_89);
lean_dec(x_81);
x_90 = lean_ctor_get(x_76, 3);
lean_inc(x_90);
lean_dec(x_76);
x_91 = lean_array_get_size(x_77);
x_92 = l_Array_toSubarray___rarg(x_77, x_90, x_91);
x_93 = lean_array_get_size(x_88);
x_94 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_95 = 0;
x_96 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_88, x_94, x_95, x_92, x_2, x_3, x_4, x_5, x_6, x_87);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_Compiler_LCNF_Simp_simp(x_89, x_2, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Compiler_LCNF_eraseParams(x_88, x_4, x_5, x_6, x_100);
lean_dec(x_88);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_77);
lean_dec(x_76);
x_110 = lean_ctor_get(x_86, 1);
lean_inc(x_110);
lean_dec(x_86);
x_111 = lean_ctor_get(x_81, 0);
lean_inc(x_111);
lean_dec(x_81);
x_112 = l_Lean_Compiler_LCNF_Simp_simp(x_111, x_2, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_20, 0);
x_123 = lean_ctor_get(x_20, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_20);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Expr_constructorApp_x3f(x_124, x_18);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_123);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_129 = x_125;
} else {
 lean_dec_ref(x_125);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_Compiler_LCNF_eraseFVarsAt(x_137, x_4, x_5, x_6, x_123);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_139);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 2);
lean_inc(x_143);
lean_dec(x_135);
x_144 = lean_ctor_get(x_130, 3);
lean_inc(x_144);
lean_dec(x_130);
x_145 = lean_array_get_size(x_131);
x_146 = l_Array_toSubarray___rarg(x_131, x_144, x_145);
x_147 = lean_array_get_size(x_142);
x_148 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_149 = 0;
x_150 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_142, x_148, x_149, x_146, x_2, x_3, x_4, x_5, x_6, x_141);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_152 = l_Lean_Compiler_LCNF_Simp_simp(x_143, x_2, x_3, x_4, x_5, x_6, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Compiler_LCNF_eraseParams(x_142, x_4, x_5, x_6, x_154);
lean_dec(x_142);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_129;
}
lean_ctor_set(x_158, 0, x_153);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_142);
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_162 = x_152;
} else {
 lean_dec_ref(x_152);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_131);
lean_dec(x_130);
x_164 = lean_ctor_get(x_140, 1);
lean_inc(x_164);
lean_dec(x_140);
x_165 = lean_ctor_get(x_135, 0);
lean_inc(x_165);
lean_dec(x_135);
x_166 = l_Lean_Compiler_LCNF_Simp_simp(x_165, x_2, x_3, x_4, x_5, x_6, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_129;
}
lean_ctor_set(x_170, 0, x_167);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_129);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_174 = x_166;
} else {
 lean_dec_ref(x_166);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_17);
if (x_176 == 0)
{
return x_17;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_17, 0);
x_178 = lean_ctor_get(x_17, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_17);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_85 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10;
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
x_39 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10;
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
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
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
x_21 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
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
x_35 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10;
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
x_47 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_8, x_13, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_5, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_1 = x_26;
x_6 = x_25;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lambda__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Compiler_LCNF_simp___closed__1;
x_4 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__5;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__7;
x_7 = 0;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1;
x_11 = l_Lean_registerTraceClass(x_10, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2;
x_14 = l_Lean_registerTraceClass(x_13, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3;
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
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__9);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__5___closed__10);
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
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065____closed__3);
res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_11065_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
