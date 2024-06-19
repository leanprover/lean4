// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpM
// Imports: Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.Renaming Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Internalize Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.DiscrM Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.Config
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Context_inlineStack___default;
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Context_config___default;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_visited___default;
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4;
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___boxed(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2;
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_inline___default;
static lean_object* l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default;
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_State_simplified___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_binderRenaming___default;
lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_used___default;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6;
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7;
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_State_subst___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_2);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStack___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_binderRenaming___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
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
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_9(x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2;
x_2 = l_ReaderT_instFunctorOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__2), 12, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
x_5 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3;
x_6 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5;
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3;
x_13 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5;
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7;
return x_1;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
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
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_apply_1(x_1, x_14);
lean_ctor_set(x_11, 0, x_15);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
x_30 = lean_ctor_get(x_11, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_31 = lean_apply_1(x_1, x_23);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_27);
x_33 = lean_st_ref_set(x_3, x_32, x_12);
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
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
lean_ctor_set_uint8(x_9, sizeof(void*)*7, x_12);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_9, 5);
x_26 = lean_ctor_get(x_9, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set(x_28, 6, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*7, x_27);
x_29 = lean_st_ref_set(x_1, x_28, x_10);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_markSimplified(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
x_29 = lean_ctor_get(x_9, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_27, x_30);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_25);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_26);
x_33 = lean_st_ref_set(x_1, x_32, x_10);
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
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incVisited(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
x_29 = lean_ctor_get(x_9, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_25);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_26);
x_33 = lean_st_ref_set(x_1, x_32, x_10);
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
lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_incInline___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInline(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
x_12 = lean_ctor_get(x_9, 6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 6, x_14);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
x_29 = lean_ctor_get(x_9, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_25);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_26);
x_33 = lean_st_ref_set(x_1, x_32, x_10);
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
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_14 = lean_ctor_get(x_11, 3);
x_15 = 2;
x_16 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_14, x_1, x_15);
lean_ctor_set(x_11, 3, x_16);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_ctor_get(x_11, 5);
x_31 = lean_ctor_get(x_11, 6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = 2;
x_33 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__3(x_27, x_1, x_32);
x_34 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*7, x_28);
x_35 = lean_st_ref_set(x_3, x_34, x_12);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(x_14, x_1);
lean_ctor_set(x_11, 3, x_15);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
x_30 = lean_ctor_get(x_11, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_31 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(x_26, x_1);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_27);
x_33 = lean_st_ref_set(x_3, x_32, x_12);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_addFunOcc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
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
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(x_14, x_1);
lean_ctor_set(x_11, 3, x_15);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*7);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
x_30 = lean_ctor_get(x_11, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_31 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(x_26, x_1);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_27);
x_33 = lean_st_ref_set(x_3, x_32, x_12);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 3);
x_16 = l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
lean_ctor_set(x_12, 3, x_16);
x_17 = lean_st_ref_set(x_4, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(x_15, x_1, x_2, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_take(x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 3);
lean_dec(x_26);
lean_ctor_set(x_23, 3, x_20);
x_27 = lean_st_ref_set(x_4, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get(x_23, 2);
x_37 = lean_ctor_get_uint8(x_23, sizeof(void*)*7);
x_38 = lean_ctor_get(x_23, 4);
x_39 = lean_ctor_get(x_23, 5);
x_40 = lean_ctor_get(x_23, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_20);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
lean_ctor_set(x_41, 6, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*7, x_37);
x_42 = lean_st_ref_set(x_4, x_41, x_24);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
x_53 = lean_ctor_get(x_12, 2);
x_54 = lean_ctor_get(x_12, 3);
x_55 = lean_ctor_get_uint8(x_12, sizeof(void*)*7);
x_56 = lean_ctor_get(x_12, 4);
x_57 = lean_ctor_get(x_12, 5);
x_58 = lean_ctor_get(x_12, 6);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_59 = l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
x_60 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*7, x_55);
x_61 = lean_st_ref_set(x_4, x_60, x_13);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(x_54, x_1, x_2, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_take(x_4, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_67, sizeof(void*)*7);
x_73 = lean_ctor_get(x_67, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 6);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 lean_ctor_release(x_67, 4);
 lean_ctor_release(x_67, 5);
 lean_ctor_release(x_67, 6);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 7, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_64);
lean_ctor_set(x_77, 4, x_73);
lean_ctor_set(x_77, 5, x_74);
lean_ctor_set(x_77, 6, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*7, x_72);
x_78 = lean_st_ref_set(x_4, x_77, x_68);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_63, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_63, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_85 = x_63;
} else {
 lean_dec_ref(x_63);
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
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_7, 2);
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
x_19 = lean_ctor_get(x_7, 2);
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
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 2);
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_23);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_7, 2);
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_31);
lean_inc(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_6, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_7, 2);
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_1);
lean_inc(x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_40;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_8, 2);
x_23 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_take(x_9, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; double x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_27, 3);
x_31 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_32 = 0;
x_33 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_34 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_float(x_34, sizeof(void*)*2, x_31);
lean_ctor_set_float(x_34, sizeof(void*)*2 + 8, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 16, x_32);
x_35 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_35);
lean_inc(x_11);
lean_ctor_set(x_25, 1, x_36);
lean_ctor_set(x_25, 0, x_11);
x_37 = l_Lean_PersistentArray_push___rarg(x_30, x_25);
lean_ctor_set(x_27, 3, x_37);
x_38 = lean_st_ref_set(x_9, x_27, x_29);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
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
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; double x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get(x_25, 1);
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
x_48 = lean_ctor_get(x_27, 2);
x_49 = lean_ctor_get(x_27, 3);
x_50 = lean_ctor_get(x_27, 4);
x_51 = lean_ctor_get(x_27, 5);
x_52 = lean_ctor_get(x_27, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_53 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_54 = 0;
x_55 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_56 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_float(x_56, sizeof(void*)*2, x_53);
lean_ctor_set_float(x_56, sizeof(void*)*2 + 8, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 16, x_54);
x_57 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_16);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_11);
lean_ctor_set(x_25, 1, x_58);
lean_ctor_set(x_25, 0, x_11);
x_59 = l_Lean_PersistentArray_push___rarg(x_49, x_25);
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_60, 2, x_48);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_50);
lean_ctor_set(x_60, 5, x_51);
lean_ctor_set(x_60, 6, x_52);
x_61 = lean_st_ref_set(x_9, x_60, x_45);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; double x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 6);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 lean_ctor_release(x_66, 5);
 lean_ctor_release(x_66, 6);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
x_76 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_77 = 0;
x_78 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_79 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_float(x_79, sizeof(void*)*2, x_76);
lean_ctor_set_float(x_79, sizeof(void*)*2 + 8, x_76);
lean_ctor_set_uint8(x_79, sizeof(void*)*2 + 16, x_77);
x_80 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_81 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_16);
lean_ctor_set(x_81, 2, x_80);
lean_inc(x_11);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_PersistentArray_push___rarg(x_71, x_82);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 7, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_68);
lean_ctor_set(x_84, 1, x_69);
lean_ctor_set(x_84, 2, x_70);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_72);
lean_ctor_set(x_84, 5, x_73);
lean_ctor_set(x_84, 6, x_74);
x_85 = lean_st_ref_set(x_9, x_84, x_67);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; double x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_90 = lean_ctor_get(x_16, 0);
x_91 = lean_ctor_get(x_16, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_16);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_92);
lean_dec(x_92);
x_94 = lean_ctor_get(x_8, 2);
x_95 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_94);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_15);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
x_97 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_2);
x_98 = lean_st_ref_take(x_9, x_91);
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
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 6);
lean_inc(x_108);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 lean_ctor_release(x_99, 6);
 x_109 = x_99;
} else {
 lean_dec_ref(x_99);
 x_109 = lean_box(0);
}
x_110 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_111 = 0;
x_112 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_113 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_float(x_113, sizeof(void*)*2, x_110);
lean_ctor_set_float(x_113, sizeof(void*)*2 + 8, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*2 + 16, x_111);
x_114 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_115 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_97);
lean_ctor_set(x_115, 2, x_114);
lean_inc(x_11);
if (lean_is_scalar(x_101)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_101;
}
lean_ctor_set(x_116, 0, x_11);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_PersistentArray_push___rarg(x_105, x_116);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 7, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_102);
lean_ctor_set(x_118, 1, x_103);
lean_ctor_set(x_118, 2, x_104);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_106);
lean_ctor_set(x_118, 5, x_107);
lean_ctor_set(x_118, 6, x_108);
x_119 = lean_st_ref_set(x_9, x_118, x_100);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function `", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been recursively inlined more than #", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", consider removing the attribute `[inline_if_reduce]` from this declaration or increasing the limit using `set_option compiler.maxRecInlineIfReduce <num>`", 155, 155);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_getConfig(x_8, x_9, x_10, x_11, x_12);
if (x_2 == 0)
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
if (x_4 == 0)
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_dec_lt(x_25, x_1);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_free_object(x_13);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_getConfig(x_8, x_9, x_10, x_11, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_MessageData_ofName(x_3);
x_32 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_31);
lean_ctor_set(x_27, 0, x_32);
x_33 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = l_Lean_MessageData_ofName(x_3);
x_50 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_47, 2);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l___private_Init_Data_Repr_0__Nat_reprFast(x_54);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_MessageData_ofFormat(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
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
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_ctor_get(x_66, 2);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_nat_dec_lt(x_68, x_1);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_3);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_71 = l_Lean_Compiler_LCNF_getConfig(x_8, x_9, x_10, x_11, x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = l_Lean_MessageData_ofName(x_3);
x_76 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2;
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_ctor_get(x_72, 2);
lean_inc(x_80);
lean_dec(x_72);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_73);
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
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(x_12, x_1);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_getDecl_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(0u);
x_15 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_15 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(x_19, x_2, x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(x_22);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(x_19, x_2, x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_4);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2;
x_3 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(x_2, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_inc(x_2);
x_21 = l_Lean_MessageData_ofName(x_2);
x_22 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_11, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(x_2, x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_dec(x_12);
lean_inc(x_2);
x_29 = l_Lean_MessageData_ofName(x_2);
x_30 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_11, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(x_2, x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_18, x_12, x_14);
lean_ctor_set(x_4, 3, x_20);
lean_ctor_set(x_4, 2, x_19);
x_21 = lean_apply_8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_25, x_12, x_14);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_apply_8(x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = lean_apply_8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_Simp_withInlining___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 2);
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_23);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_7, 2);
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_31);
lean_inc(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_6, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_7, 2);
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_1);
lean_inc(x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_40;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("...\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_name_eq(x_23, x_17);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_19);
x_25 = 1;
lean_inc(x_17);
x_26 = l_Lean_Name_toString(x_17, x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_1);
lean_inc(x_2);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_14, 1, x_17);
lean_ctor_set(x_14, 0, x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_4, 0, x_31);
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = lean_unbox(x_19);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_19);
x_34 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_34);
lean_ctor_set(x_3, 0, x_22);
lean_ctor_set(x_14, 0, x_3);
x_35 = 1;
x_36 = lean_box(x_35);
lean_ctor_set(x_4, 0, x_36);
x_3 = x_18;
goto _start;
}
else
{
lean_free_object(x_3);
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_name_eq(x_40, x_17);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_19);
x_42 = 1;
lean_inc(x_17);
x_43 = l_Lean_Name_toString(x_17, x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_44);
lean_ctor_set(x_3, 0, x_1);
lean_inc(x_2);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_2);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
x_48 = 0;
x_49 = lean_box(x_48);
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_49);
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_17);
x_51 = lean_unbox(x_19);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
lean_dec(x_19);
x_52 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_52);
lean_ctor_set(x_3, 0, x_39);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_40);
x_54 = 1;
x_55 = lean_box(x_54);
lean_ctor_set(x_4, 1, x_53);
lean_ctor_set(x_4, 0, x_55);
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_57; 
lean_free_object(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_39);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set(x_4, 1, x_57);
x_3 = x_18;
goto _start;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_64 = x_14;
} else {
 lean_dec_ref(x_14);
 x_64 = lean_box(0);
}
x_65 = lean_name_eq(x_63, x_59);
if (x_65 == 0)
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
lean_dec(x_61);
x_66 = 1;
lean_inc(x_59);
x_67 = l_Lean_Name_toString(x_59, x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_68);
lean_ctor_set(x_3, 0, x_1);
lean_inc(x_2);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_2);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_64)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_64;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_59);
x_72 = 0;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
x_3 = x_60;
x_4 = x_74;
goto _start;
}
else
{
uint8_t x_76; 
lean_dec(x_59);
x_76 = lean_unbox(x_61);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
x_77 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_77);
lean_ctor_set(x_3, 0, x_62);
if (lean_is_scalar(x_64)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_64;
}
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_63);
x_79 = 1;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_3 = x_60;
x_4 = x_81;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_3);
if (lean_is_scalar(x_64)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_64;
}
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_63);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_61);
lean_ctor_set(x_84, 1, x_83);
x_3 = x_60;
x_4 = x_84;
goto _start;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_3, 0);
x_87 = lean_ctor_get(x_3, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_3);
x_88 = lean_ctor_get(x_4, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_89 = x_4;
} else {
 lean_dec_ref(x_4);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_14, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_92 = x_14;
} else {
 lean_dec_ref(x_14);
 x_92 = lean_box(0);
}
x_93 = lean_name_eq(x_91, x_86);
if (x_93 == 0)
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_91);
lean_dec(x_88);
x_94 = 1;
lean_inc(x_86);
x_95 = l_Lean_Name_toString(x_86, x_94);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_inc(x_1);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_2);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_2);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_92)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_92;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_86);
x_101 = 0;
x_102 = lean_box(x_101);
if (lean_is_scalar(x_89)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_89;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
x_3 = x_87;
x_4 = x_103;
goto _start;
}
else
{
uint8_t x_105; 
lean_dec(x_86);
x_105 = lean_unbox(x_88);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_88);
x_106 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_92)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_92;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_91);
x_109 = 1;
x_110 = lean_box(x_109);
if (lean_is_scalar(x_89)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_89;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_3 = x_87;
x_4 = x_111;
goto _start;
}
else
{
lean_object* x_113; lean_object* x_114; 
if (lean_is_scalar(x_92)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_92;
}
lean_ctor_set(x_113, 0, x_90);
lean_ctor_set(x_113, 1, x_91);
if (lean_is_scalar(x_89)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_89;
}
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_113);
x_3 = x_87;
x_4 = x_114;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_7, 2);
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_23);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_7, 2);
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 0, x_31);
lean_inc(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_6, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_7, 2);
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_1);
lean_inc(x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_40;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth reached in the code generator\nfunction inline stack:\n", 77, 77);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2;
x_11 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = 1;
lean_inc(x_13);
x_16 = l_Lean_Name_toString(x_13, x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_18);
x_19 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(x_18, x_19, x_14, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_dec(x_33);
x_34 = l_Lean_MessageData_ofFormat(x_32);
x_35 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_34);
lean_ctor_set(x_28, 0, x_35);
x_36 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_28);
x_37 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_42);
lean_ctor_set(x_26, 0, x_41);
x_43 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_1);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec(x_26);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = l_Lean_MessageData_ofFormat(x_46);
x_49 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(7, 2, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 7);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(x_52, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_1);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_56 = 1;
lean_inc(x_54);
x_57 = l_Lean_Name_toString(x_54, x_56);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_67 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(x_59, x_61, x_55, x_66, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
x_74 = l_Lean_MessageData_ofFormat(x_72);
x_75 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(7, 2, 0);
} else {
 x_76 = x_73;
 lean_ctor_set_tag(x_76, 7);
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(7, 2, 0);
} else {
 x_78 = x_70;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(x_78, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_71);
lean_dec(x_1);
return x_79;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 10);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_22 = lean_ctor_get(x_7, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
x_24 = lean_nat_dec_eq(x_13, x_14);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_7, 11);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 10);
lean_dec(x_27);
x_28 = lean_ctor_get(x_7, 9);
lean_dec(x_28);
x_29 = lean_ctor_get(x_7, 8);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 7);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 6);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 5);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_7, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_7, 0);
lean_dec(x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_13, x_38);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_39);
x_40 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_13, x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_11);
lean_ctor_set(x_43, 2, x_12);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_14);
lean_ctor_set(x_43, 5, x_15);
lean_ctor_set(x_43, 6, x_16);
lean_ctor_set(x_43, 7, x_17);
lean_ctor_set(x_43, 8, x_18);
lean_ctor_set(x_43, 9, x_19);
lean_ctor_set(x_43, 10, x_20);
lean_ctor_set(x_43, 11, x_22);
lean_ctor_set_uint8(x_43, sizeof(void*)*12, x_21);
lean_ctor_set_uint8(x_43, sizeof(void*)*12 + 1, x_23);
x_44 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_43, x_8, x_9);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_45 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Simp_addMustInline(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_14, x_1);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_4);
x_18 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 3);
x_26 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_25, x_1, x_16);
lean_ctor_set(x_22, 3, x_26);
x_27 = lean_st_ref_set(x_4, x_22, x_23);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
x_36 = lean_ctor_get_uint8(x_22, sizeof(void*)*7);
x_37 = lean_ctor_get(x_22, 4);
x_38 = lean_ctor_get(x_22, 5);
x_39 = lean_ctor_get(x_22, 6);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_40 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_35, x_1, x_16);
x_41 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_37);
lean_ctor_set(x_41, 5, x_38);
lean_ctor_set(x_41, 6, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*7, x_36);
x_42 = lean_st_ref_set(x_4, x_41, x_23);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_st_ref_take(x_4, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_49, 3);
x_53 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_52, x_1, x_16);
lean_ctor_set(x_49, 3, x_53);
x_54 = lean_st_ref_set(x_4, x_49, x_50);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_46);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_49, 0);
x_60 = lean_ctor_get(x_49, 1);
x_61 = lean_ctor_get(x_49, 2);
x_62 = lean_ctor_get(x_49, 3);
x_63 = lean_ctor_get_uint8(x_49, sizeof(void*)*7);
x_64 = lean_ctor_get(x_49, 4);
x_65 = lean_ctor_get(x_49, 5);
x_66 = lean_ctor_get(x_49, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_49);
x_67 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_62, x_1, x_16);
x_68 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*7, x_63);
x_69 = lean_st_ref_set(x_4, x_68, x_50);
lean_dec(x_4);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_46);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_13, x_1);
lean_dec(x_13);
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
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_24, x_1);
lean_dec(x_24);
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
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Compiler_LCNF_getConfig(x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Code_sizeLe(x_1, x_13);
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
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_Code_sizeLe(x_1, x_18);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_isSmall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 4);
x_16 = l_Lean_Compiler_LCNF_Simp_isSmall(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_25 = lean_ctor_get(x_17, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_array_fget(x_19, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_20, x_29);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_30);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lean_Compiler_LCNF_Arg_toExpr(x_28);
x_33 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_31, x_32);
lean_ctor_set(x_4, 1, x_33);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_17);
x_37 = lean_array_fget(x_19, x_20);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_20, x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_21);
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_41);
lean_dec(x_15);
x_42 = l_Lean_Compiler_LCNF_Arg_toExpr(x_37);
x_43 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_41, x_42);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_40);
x_44 = 1;
x_45 = lean_usize_add(x_3, x_44);
x_3 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_4, 0);
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_4);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_15);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_12);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; 
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
 x_55 = lean_box(0);
}
x_56 = lean_array_fget(x_49, x_50);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_50, x_57);
lean_dec(x_50);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 3, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_51);
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = l_Lean_Compiler_LCNF_Arg_toExpr(x_56);
x_62 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_48, x_60, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = 1;
x_65 = lean_usize_add(x_3, x_64);
x_3 = x_65;
x_4 = x_63;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_array_get_size(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_toSubarray___rarg(x_3, x_14, x_13);
x_16 = l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_get_size(x_1);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_19, x_20, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_Code_internalize(x_2, x_24, x_8, x_9, x_10, x_11, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_26);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Compiler_LCNF_eraseLetDecl(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 1;
x_11 = l_Lean_Compiler_LCNF_eraseFunDecl(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_2);
x_16 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_1);
x_17 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_15, x_1, x_16);
lean_ctor_set(x_12, 0, x_17);
x_18 = lean_st_ref_set(x_4, x_12, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_getBinderName(x_1, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Name_isInternal(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_20);
lean_inc(x_2);
x_25 = l_Lean_Compiler_LCNF_getBinderName(x_2, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lean_Name_isInternal(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_2);
x_30 = lean_box(0);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_free_object(x_25);
x_31 = lean_st_ref_take(x_4, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_32, 2);
x_36 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_35, x_2, x_22);
lean_ctor_set(x_32, 2, x_36);
x_37 = lean_st_ref_set(x_4, x_32, x_33);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
x_46 = lean_ctor_get(x_32, 2);
x_47 = lean_ctor_get(x_32, 3);
x_48 = lean_ctor_get_uint8(x_32, sizeof(void*)*7);
x_49 = lean_ctor_get(x_32, 4);
x_50 = lean_ctor_get(x_32, 5);
x_51 = lean_ctor_get(x_32, 6);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_52 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_46, x_2, x_22);
x_53 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_50);
lean_ctor_set(x_53, 6, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*7, x_48);
x_54 = lean_st_ref_set(x_4, x_53, x_33);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = l_Lean_Name_isInternal(x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_22);
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_64 = lean_st_ref_take(x_4, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_65, sizeof(void*)*7);
x_72 = lean_ctor_get(x_65, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 6);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_69, x_2, x_22);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 7, 1);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_70);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_77, 5, x_73);
lean_ctor_set(x_77, 6, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*7, x_71);
x_78 = lean_st_ref_set(x_4, x_77, x_66);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_22);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_25);
if (x_83 == 0)
{
return x_25;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_25, 0);
x_85 = lean_ctor_get(x_25, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_25);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_22);
lean_dec(x_2);
x_87 = lean_box(0);
lean_ctor_set(x_20, 0, x_87);
return x_20;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_20, 0);
x_89 = lean_ctor_get(x_20, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_20);
x_90 = l_Lean_Name_isInternal(x_88);
if (x_90 == 0)
{
lean_object* x_91; 
lean_inc(x_2);
x_91 = l_Lean_Compiler_LCNF_getBinderName(x_2, x_6, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Name_isInternal(x_92);
lean_dec(x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
lean_dec(x_2);
x_96 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_94);
x_98 = lean_st_ref_take(x_4, x_93);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 3);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_99, sizeof(void*)*7);
x_106 = lean_ctor_get(x_99, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 6);
lean_inc(x_108);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 lean_ctor_release(x_99, 6);
 x_109 = x_99;
} else {
 lean_dec_ref(x_99);
 x_109 = lean_box(0);
}
x_110 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_103, x_2, x_88);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 7, 1);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_104);
lean_ctor_set(x_111, 4, x_106);
lean_ctor_set(x_111, 5, x_107);
lean_ctor_set(x_111, 6, x_108);
lean_ctor_set_uint8(x_111, sizeof(void*)*7, x_105);
x_112 = lean_st_ref_set(x_4, x_111, x_100);
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
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_88);
lean_dec(x_2);
x_117 = lean_ctor_get(x_91, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_91, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_119 = x_91;
} else {
 lean_dec_ref(x_91);
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
lean_object* x_121; lean_object* x_122; 
lean_dec(x_88);
lean_dec(x_2);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_89);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_20);
if (x_123 == 0)
{
return x_20;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_20, 0);
x_125 = lean_ctor_get(x_20, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_20);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_127 = lean_ctor_get(x_12, 0);
x_128 = lean_ctor_get(x_12, 1);
x_129 = lean_ctor_get(x_12, 2);
x_130 = lean_ctor_get(x_12, 3);
x_131 = lean_ctor_get_uint8(x_12, sizeof(void*)*7);
x_132 = lean_ctor_get(x_12, 4);
x_133 = lean_ctor_get(x_12, 5);
x_134 = lean_ctor_get(x_12, 6);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_12);
lean_inc(x_2);
x_135 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_1);
x_136 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_127, x_1, x_135);
x_137 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_129);
lean_ctor_set(x_137, 3, x_130);
lean_ctor_set(x_137, 4, x_132);
lean_ctor_set(x_137, 5, x_133);
lean_ctor_set(x_137, 6, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*7, x_131);
x_138 = lean_st_ref_set(x_4, x_137, x_13);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Lean_Compiler_LCNF_getBinderName(x_1, x_6, x_7, x_8, x_9, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
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
x_144 = l_Lean_Name_isInternal(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_143);
lean_inc(x_2);
x_145 = l_Lean_Compiler_LCNF_getBinderName(x_2, x_6, x_7, x_8, x_9, x_142);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Name_isInternal(x_146);
lean_dec(x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_141);
lean_dec(x_2);
x_150 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_147);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_148);
x_152 = lean_st_ref_take(x_4, x_147);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 3);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_153, sizeof(void*)*7);
x_160 = lean_ctor_get(x_153, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_153, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_153, 6);
lean_inc(x_162);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 lean_ctor_release(x_153, 4);
 lean_ctor_release(x_153, 5);
 lean_ctor_release(x_153, 6);
 x_163 = x_153;
} else {
 lean_dec_ref(x_153);
 x_163 = lean_box(0);
}
x_164 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_157, x_2, x_141);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 7, 1);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_156);
lean_ctor_set(x_165, 2, x_164);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_165, 4, x_160);
lean_ctor_set(x_165, 5, x_161);
lean_ctor_set(x_165, 6, x_162);
lean_ctor_set_uint8(x_165, sizeof(void*)*7, x_159);
x_166 = lean_st_ref_set(x_4, x_165, x_154);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_141);
lean_dec(x_2);
x_171 = lean_ctor_get(x_145, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_145, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_173 = x_145;
} else {
 lean_dec_ref(x_145);
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
lean_object* x_175; lean_object* x_176; 
lean_dec(x_141);
lean_dec(x_2);
x_175 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_143;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_142);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_2);
x_177 = lean_ctor_get(x_140, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_140, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_179 = x_140;
} else {
 lean_dec_ref(x_140);
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
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Renaming(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_config___default___closed__1);
l_Lean_Compiler_LCNF_Simp_Context_config___default = _init_l_Lean_Compiler_LCNF_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_config___default);
l_Lean_Compiler_LCNF_Simp_Context_inlineStack___default = _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStack___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_inlineStack___default);
l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__1);
l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default___closed__2);
l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default = _init_l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_Context_inlineStackOccs___default);
l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_subst___default___closed__1);
l_Lean_Compiler_LCNF_Simp_State_subst___default = _init_l_Lean_Compiler_LCNF_Simp_State_subst___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_subst___default);
l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_used___default___closed__1);
l_Lean_Compiler_LCNF_Simp_State_used___default = _init_l_Lean_Compiler_LCNF_Simp_State_used___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_used___default);
l_Lean_Compiler_LCNF_Simp_State_binderRenaming___default = _init_l_Lean_Compiler_LCNF_Simp_State_binderRenaming___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_binderRenaming___default);
l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default = _init_l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_funDeclInfoMap___default);
l_Lean_Compiler_LCNF_Simp_State_simplified___default = _init_l_Lean_Compiler_LCNF_Simp_State_simplified___default();
l_Lean_Compiler_LCNF_Simp_State_visited___default = _init_l_Lean_Compiler_LCNF_Simp_State_visited___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_visited___default);
l_Lean_Compiler_LCNF_Simp_State_inline___default = _init_l_Lean_Compiler_LCNF_Simp_State_inline___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_inline___default);
l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default = _init_l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_State_inlineLocal___default);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1();
l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5);
l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6);
l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2);
l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4);
l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1);
l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2 = _init_l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6);
l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7 = _init_l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
