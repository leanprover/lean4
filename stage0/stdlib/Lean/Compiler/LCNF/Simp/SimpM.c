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
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__6;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6;
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__2;
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___closed__5;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__2;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMFalse(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_markSimplified(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incVisited(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInline(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Simp_incInlineLocal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(x_14, x_1);
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
x_31 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(x_26, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3;
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
x_59 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = l_Lean_isTracingEnabledForCore(x_1, x_10, x_9);
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
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2;
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
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_8, 2);
x_23 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 3);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; double x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_36 = 0;
x_37 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_35);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_36);
x_39 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_40 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_11);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_11);
x_41 = l_Lean_PersistentArray_push___rarg(x_34, x_25);
lean_ctor_set(x_27, 0, x_41);
x_42 = lean_st_ref_set(x_9, x_26, x_29);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint64_t x_49; lean_object* x_50; double x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_49 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
lean_dec(x_27);
x_51 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_52 = 0;
x_53 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_54 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_float(x_54, sizeof(void*)*2, x_51);
lean_ctor_set_float(x_54, sizeof(void*)*2 + 8, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 16, x_52);
x_55 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_56 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_16);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_11);
lean_ctor_set(x_25, 1, x_56);
lean_ctor_set(x_25, 0, x_11);
x_57 = l_Lean_PersistentArray_push___rarg(x_50, x_25);
x_58 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint64(x_58, sizeof(void*)*1, x_49);
lean_ctor_set(x_26, 3, x_58);
x_59 = lean_st_ref_set(x_9, x_26, x_29);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; double x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
x_66 = lean_ctor_get(x_26, 2);
x_67 = lean_ctor_get(x_26, 4);
x_68 = lean_ctor_get(x_26, 5);
x_69 = lean_ctor_get(x_26, 6);
x_70 = lean_ctor_get(x_26, 7);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_71 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
x_72 = lean_ctor_get(x_27, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_73 = x_27;
} else {
 lean_dec_ref(x_27);
 x_73 = lean_box(0);
}
x_74 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_75 = 0;
x_76 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_77 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_float(x_77, sizeof(void*)*2, x_74);
lean_ctor_set_float(x_77, sizeof(void*)*2 + 8, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 16, x_75);
x_78 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_79 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_16);
lean_ctor_set(x_79, 2, x_78);
lean_inc(x_11);
lean_ctor_set(x_25, 1, x_79);
lean_ctor_set(x_25, 0, x_11);
x_80 = l_Lean_PersistentArray_push___rarg(x_72, x_25);
if (lean_is_scalar(x_73)) {
 x_81 = lean_alloc_ctor(0, 1, 8);
} else {
 x_81 = x_73;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint64(x_81, sizeof(void*)*1, x_71);
x_82 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_82, 0, x_64);
lean_ctor_set(x_82, 1, x_65);
lean_ctor_set(x_82, 2, x_66);
lean_ctor_set(x_82, 3, x_81);
lean_ctor_set(x_82, 4, x_67);
lean_ctor_set(x_82, 5, x_68);
lean_ctor_set(x_82, 6, x_69);
lean_ctor_set(x_82, 7, x_70);
x_83 = lean_st_ref_set(x_9, x_82, x_29);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; lean_object* x_99; double x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_88 = lean_ctor_get(x_25, 1);
lean_inc(x_88);
lean_dec(x_25);
x_89 = lean_ctor_get(x_26, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_26, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_26, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_26, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_26, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_26, 7);
lean_inc(x_95);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 x_96 = x_26;
} else {
 lean_dec_ref(x_26);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get_uint64(x_27, sizeof(void*)*1);
x_98 = lean_ctor_get(x_27, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_99 = x_27;
} else {
 lean_dec_ref(x_27);
 x_99 = lean_box(0);
}
x_100 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_101 = 0;
x_102 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_103 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_float(x_103, sizeof(void*)*2, x_100);
lean_ctor_set_float(x_103, sizeof(void*)*2 + 8, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 16, x_101);
x_104 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_105 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_16);
lean_ctor_set(x_105, 2, x_104);
lean_inc(x_11);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_11);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_PersistentArray_push___rarg(x_98, x_106);
if (lean_is_scalar(x_99)) {
 x_108 = lean_alloc_ctor(0, 1, 8);
} else {
 x_108 = x_99;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set_uint64(x_108, sizeof(void*)*1, x_97);
if (lean_is_scalar(x_96)) {
 x_109 = lean_alloc_ctor(0, 8, 0);
} else {
 x_109 = x_96;
}
lean_ctor_set(x_109, 0, x_89);
lean_ctor_set(x_109, 1, x_90);
lean_ctor_set(x_109, 2, x_91);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_109, 4, x_92);
lean_ctor_set(x_109, 5, x_93);
lean_ctor_set(x_109, 6, x_94);
lean_ctor_set(x_109, 7, x_95);
x_110 = lean_st_ref_set(x_9, x_109, x_88);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; lean_object* x_137; lean_object* x_138; double x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_115 = lean_ctor_get(x_16, 0);
x_116 = lean_ctor_get(x_16, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_16);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_117);
lean_dec(x_117);
x_119 = lean_ctor_get(x_8, 2);
x_120 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
lean_inc(x_119);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_15);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
x_122 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_2);
x_123 = lean_st_ref_take(x_9, x_116);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 5);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 6);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 7);
lean_inc(x_134);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 lean_ctor_release(x_124, 6);
 lean_ctor_release(x_124, 7);
 x_135 = x_124;
} else {
 lean_dec_ref(x_124);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get_uint64(x_125, sizeof(void*)*1);
x_137 = lean_ctor_get(x_125, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
x_139 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__1;
x_140 = 0;
x_141 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__2;
x_142 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_float(x_142, sizeof(void*)*2, x_139);
lean_ctor_set_float(x_142, sizeof(void*)*2 + 8, x_139);
lean_ctor_set_uint8(x_142, sizeof(void*)*2 + 16, x_140);
x_143 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3___closed__3;
x_144 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_122);
lean_ctor_set(x_144, 2, x_143);
lean_inc(x_11);
if (lean_is_scalar(x_127)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_127;
}
lean_ctor_set(x_145, 0, x_11);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_PersistentArray_push___rarg(x_137, x_145);
if (lean_is_scalar(x_138)) {
 x_147 = lean_alloc_ctor(0, 1, 8);
} else {
 x_147 = x_138;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set_uint64(x_147, sizeof(void*)*1, x_136);
if (lean_is_scalar(x_135)) {
 x_148 = lean_alloc_ctor(0, 8, 0);
} else {
 x_148 = x_135;
}
lean_ctor_set(x_148, 0, x_128);
lean_ctor_set(x_148, 1, x_129);
lean_ctor_set(x_148, 2, x_130);
lean_ctor_set(x_148, 3, x_147);
lean_ctor_set(x_148, 4, x_131);
lean_ctor_set(x_148, 5, x_132);
lean_ctor_set(x_148, 6, x_133);
lean_ctor_set(x_148, 7, x_134);
x_149 = lean_st_ref_set(x_9, x_148, x_126);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
return x_153;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(x_12, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_18, x_12, x_14);
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
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_25, x_12, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("...\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_name_eq(x_28, x_22);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_24);
x_30 = 1;
lean_inc(x_3);
lean_inc(x_22);
x_31 = l_Lean_Name_toString(x_22, x_30, x_3);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_2);
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_32);
lean_ctor_set(x_7, 0, x_2);
lean_inc(x_4);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_8, 0, x_36);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
x_38 = lean_unbox(x_24);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_24);
x_39 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_27);
lean_ctor_set(x_19, 0, x_7);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_8, 0, x_41);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_free_object(x_7);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_name_eq(x_45, x_22);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_45);
lean_dec(x_24);
x_47 = 1;
lean_inc(x_3);
lean_inc(x_22);
x_48 = l_Lean_Name_toString(x_22, x_47, x_3);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_inc(x_2);
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_49);
lean_ctor_set(x_7, 0, x_2);
lean_inc(x_4);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_4);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_22);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_8, 1, x_52);
lean_ctor_set(x_8, 0, x_54);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_22);
x_56 = lean_unbox(x_24);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_24);
x_57 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_57);
lean_ctor_set(x_7, 0, x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_45);
x_59 = 1;
x_60 = lean_box(x_59);
lean_ctor_set(x_8, 1, x_58);
lean_ctor_set(x_8, 0, x_60);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_62; 
lean_free_object(x_7);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_45);
lean_ctor_set(x_8, 1, x_62);
x_7 = x_23;
x_9 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
x_66 = lean_ctor_get(x_8, 0);
lean_inc(x_66);
lean_dec(x_8);
x_67 = lean_ctor_get(x_19, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_69 = x_19;
} else {
 lean_dec_ref(x_19);
 x_69 = lean_box(0);
}
x_70 = lean_name_eq(x_68, x_64);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
lean_dec(x_66);
x_71 = 1;
lean_inc(x_3);
lean_inc(x_64);
x_72 = l_Lean_Name_toString(x_64, x_71, x_3);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_inc(x_2);
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_73);
lean_ctor_set(x_7, 0, x_2);
lean_inc(x_4);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_7);
lean_ctor_set(x_74, 1, x_4);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_69;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_64);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
x_7 = x_65;
x_8 = x_79;
x_9 = lean_box(0);
goto _start;
}
else
{
uint8_t x_81; 
lean_dec(x_64);
x_81 = lean_unbox(x_66);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_66);
x_82 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_82);
lean_ctor_set(x_7, 0, x_67);
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_7);
lean_ctor_set(x_83, 1, x_68);
x_84 = 1;
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_7 = x_65;
x_8 = x_86;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_free_object(x_7);
if (lean_is_scalar(x_69)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_69;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_88);
x_7 = x_65;
x_8 = x_89;
x_9 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_7, 0);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_7);
x_93 = lean_ctor_get(x_8, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_94 = x_8;
} else {
 lean_dec_ref(x_8);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_19, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_97 = x_19;
} else {
 lean_dec_ref(x_19);
 x_97 = lean_box(0);
}
x_98 = lean_name_eq(x_96, x_91);
if (x_98 == 0)
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_93);
x_99 = 1;
lean_inc(x_3);
lean_inc(x_91);
x_100 = l_Lean_Name_toString(x_91, x_99, x_3);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_inc(x_2);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_4);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_4);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_97)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_97;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_91);
x_106 = 0;
x_107 = lean_box(x_106);
if (lean_is_scalar(x_94)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_94;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
x_7 = x_92;
x_8 = x_108;
x_9 = lean_box(0);
goto _start;
}
else
{
uint8_t x_110; 
lean_dec(x_91);
x_110 = lean_unbox(x_93);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
x_111 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_95);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_97)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_97;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_96);
x_114 = 1;
x_115 = lean_box(x_114);
if (lean_is_scalar(x_94)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_94;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
x_7 = x_92;
x_8 = x_116;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; 
if (lean_is_scalar(x_97)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_97;
}
lean_ctor_set(x_118, 0, x_95);
lean_ctor_set(x_118, 1, x_96);
if (lean_is_scalar(x_94)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_94;
}
lean_ctor_set(x_119, 0, x_93);
lean_ctor_set(x_119, 1, x_118);
x_7 = x_92;
x_8 = x_119;
x_9 = lean_box(0);
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
x_28 = lean_name_eq(x_27, x_21);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_23);
x_29 = 1;
x_30 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_21);
x_31 = l_Lean_Name_toString(x_21, x_29, x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_2);
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_32);
lean_ctor_set(x_6, 0, x_2);
lean_inc(x_3);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_18, 1, x_21);
lean_ctor_set(x_18, 0, x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_7, 0, x_36);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
x_38 = lean_unbox(x_23);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_23);
x_39 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_39);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_18, 0, x_6);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_7, 0, x_41);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_free_object(x_6);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_name_eq(x_45, x_21);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
lean_dec(x_45);
lean_dec(x_23);
x_47 = 1;
x_48 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_21);
x_49 = l_Lean_Name_toString(x_21, x_47, x_48);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_inc(x_2);
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_50);
lean_ctor_set(x_6, 0, x_2);
lean_inc(x_3);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_3);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_21);
x_54 = 0;
x_55 = lean_box(x_54);
lean_ctor_set(x_7, 1, x_53);
lean_ctor_set(x_7, 0, x_55);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_21);
x_57 = lean_unbox(x_23);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
lean_dec(x_23);
x_58 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_58);
lean_ctor_set(x_6, 0, x_44);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_45);
x_60 = 1;
x_61 = lean_box(x_60);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_61);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_63; 
lean_free_object(x_6);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_45);
lean_ctor_set(x_7, 1, x_63);
x_6 = x_22;
x_8 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_6, 0);
x_66 = lean_ctor_get(x_6, 1);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = lean_name_eq(x_69, x_65);
if (x_71 == 0)
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
lean_dec(x_67);
x_72 = 1;
x_73 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_65);
x_74 = l_Lean_Name_toString(x_65, x_72, x_73);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_2);
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_75);
lean_ctor_set(x_6, 0, x_2);
lean_inc(x_3);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_3);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
x_79 = 0;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_6 = x_66;
x_7 = x_81;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_83; 
lean_dec(x_65);
x_83 = lean_unbox(x_67);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_67);
x_84 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_84);
lean_ctor_set(x_6, 0, x_68);
if (lean_is_scalar(x_70)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_70;
}
lean_ctor_set(x_85, 0, x_6);
lean_ctor_set(x_85, 1, x_69);
x_86 = 1;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_6 = x_66;
x_7 = x_88;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_free_object(x_6);
if (lean_is_scalar(x_70)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_70;
}
lean_ctor_set(x_90, 0, x_68);
lean_ctor_set(x_90, 1, x_69);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_67);
lean_ctor_set(x_91, 1, x_90);
x_6 = x_66;
x_7 = x_91;
x_8 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_93 = lean_ctor_get(x_6, 0);
x_94 = lean_ctor_get(x_6, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_6);
x_95 = lean_ctor_get(x_7, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_96 = x_7;
} else {
 lean_dec_ref(x_7);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_18, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_18, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_99 = x_18;
} else {
 lean_dec_ref(x_18);
 x_99 = lean_box(0);
}
x_100 = lean_name_eq(x_98, x_93);
if (x_100 == 0)
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
lean_dec(x_95);
x_101 = 1;
x_102 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_93);
x_103 = l_Lean_Name_toString(x_93, x_101, x_102);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_inc(x_2);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_2);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_3);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_3);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_99)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_99;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_93);
x_109 = 0;
x_110 = lean_box(x_109);
if (lean_is_scalar(x_96)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_96;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_6 = x_94;
x_7 = x_111;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_113; 
lean_dec(x_93);
x_113 = lean_unbox(x_95);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_95);
x_114 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2;
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_97);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_99)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_99;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_98);
x_117 = 1;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_96)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_96;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
x_6 = x_94;
x_7 = x_119;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_99)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_99;
}
lean_ctor_set(x_121, 0, x_97);
lean_ctor_set(x_121, 1, x_98);
if (lean_is_scalar(x_96)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_96;
}
lean_ctor_set(x_122, 0, x_95);
lean_ctor_set(x_122, 1, x_121);
x_6 = x_94;
x_7 = x_122;
x_8 = lean_box(0);
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_30 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg___boxed), 9, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = 1;
x_16 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_13);
x_17 = l_Lean_Name_toString(x_13, x_15, x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
x_20 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_13);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_inc(x_14);
x_27 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(x_14, x_19, x_20, x_22, x_14, x_14, x_26, lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_dec(x_35);
x_36 = l_Lean_MessageData_ofFormat(x_34);
x_37 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_37);
x_38 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_38);
lean_ctor_set(x_28, 0, x_30);
x_39 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_44);
lean_ctor_set(x_28, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_1);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_dec(x_27);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Lean_MessageData_ofFormat(x_48);
x_51 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(7, 2, 0);
} else {
 x_52 = x_49;
 lean_ctor_set_tag(x_52, 7);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(x_54, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_1);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = 1;
x_59 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1;
lean_inc(x_56);
x_60 = l_Lean_Name_toString(x_56, x_58, x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__3;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__5;
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_56);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
lean_inc(x_57);
x_71 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(x_57, x_62, x_64, x_66, x_57, x_57, x_70, lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_57);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = l_Lean_MessageData_ofFormat(x_76);
x_79 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___closed__7;
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_77;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(7, 2, 0);
} else {
 x_82 = x_74;
 lean_ctor_set_tag(x_82, 7);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(x_82, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
lean_dec(x_1);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___boxed(lean_object** _args) {
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
x_18 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withIncRecDepth___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_16);
x_18 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
lean_dec(x_16);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_1, x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_4);
x_33 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
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
x_40 = lean_ctor_get(x_37, 3);
x_41 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_40, x_1, x_31);
lean_ctor_set(x_37, 3, x_41);
x_42 = lean_st_ref_set(x_4, x_37, x_38);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_34);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
x_49 = lean_ctor_get(x_37, 2);
x_50 = lean_ctor_get(x_37, 3);
x_51 = lean_ctor_get_uint8(x_37, sizeof(void*)*7);
x_52 = lean_ctor_get(x_37, 4);
x_53 = lean_ctor_get(x_37, 5);
x_54 = lean_ctor_get(x_37, 6);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_55 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_50, x_1, x_31);
x_56 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set(x_56, 5, x_53);
lean_ctor_set(x_56, 6, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*7, x_51);
x_57 = lean_st_ref_set(x_4, x_56, x_38);
lean_dec(x_4);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_34);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_33, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_dec(x_33);
x_63 = lean_st_ref_take(x_4, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_64, 3);
x_68 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_67, x_1, x_31);
lean_ctor_set(x_64, 3, x_68);
x_69 = lean_st_ref_set(x_4, x_64, x_65);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_61);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_64, 0);
x_75 = lean_ctor_get(x_64, 1);
x_76 = lean_ctor_get(x_64, 2);
x_77 = lean_ctor_get(x_64, 3);
x_78 = lean_ctor_get_uint8(x_64, sizeof(void*)*7);
x_79 = lean_ctor_get(x_64, 4);
x_80 = lean_ctor_get(x_64, 5);
x_81 = lean_ctor_get(x_64, 6);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_64);
x_82 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(x_77, x_1, x_31);
x_83 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_76);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_79);
lean_ctor_set(x_83, 5, x_80);
lean_ctor_set(x_83, 6, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*7, x_78);
x_84 = lean_st_ref_set(x_4, x_83, x_65);
lean_dec(x_4);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_61);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withAddMustInline___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
lean_dec(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_1, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
if (lean_obj_tag(x_33) == 1)
{
uint8_t x_34; lean_object* x_35; 
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_10, 0, x_35);
return x_10;
}
else
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_33);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_10, 0, x_37);
return x_10;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_array_get_size(x_39);
x_41 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_39, x_52);
lean_dec(x_39);
x_54 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add___spec__1(x_1, x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
lean_dec(x_54);
if (lean_obj_tag(x_58) == 1)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_38);
return x_61;
}
else
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_58);
x_62 = 1;
x_63 = lean_box(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_38);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_4, x_6);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_20, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_22, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
lean_ctor_set(x_20, 1, x_33);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = l_Lean_Compiler_LCNF_Arg_toExpr(x_31);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
x_39 = lean_array_get_size(x_38);
x_40 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_34, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_nat_add(x_37, x_32);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_array_uset(x_38, x_51, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; size_t x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_56);
lean_ctor_set(x_21, 1, x_63);
lean_ctor_set(x_21, 0, x_54);
x_64 = lean_usize_add(x_6, x_49);
x_6 = x_64;
goto _start;
}
else
{
size_t x_66; 
lean_ctor_set(x_21, 1, x_56);
lean_ctor_set(x_21, 0, x_54);
x_66 = lean_usize_add(x_6, x_49);
x_6 = x_66;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; 
lean_inc(x_2);
x_68 = lean_array_uset(x_38, x_51, x_2);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_34, x_35, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
lean_ctor_set(x_21, 1, x_70);
x_71 = lean_usize_add(x_6, x_49);
x_6 = x_71;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = lean_array_get_size(x_74);
x_76 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_34, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_73, x_32);
lean_dec(x_73);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_34);
lean_ctor_set(x_91, 1, x_35);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_74, x_87, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; size_t x_101; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_7, 1, x_100);
x_101 = lean_usize_add(x_6, x_85);
x_6 = x_101;
goto _start;
}
else
{
lean_object* x_103; size_t x_104; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_92);
lean_ctor_set(x_7, 1, x_103);
x_104 = lean_usize_add(x_6, x_85);
x_6 = x_104;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; 
lean_inc(x_2);
x_106 = lean_array_uset(x_74, x_87, x_2);
x_107 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_34, x_35, x_88);
x_108 = lean_array_uset(x_106, x_87, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_73);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_7, 1, x_109);
x_110 = lean_usize_add(x_6, x_85);
x_6 = x_110;
goto _start;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_20);
x_112 = lean_array_fget(x_22, x_23);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_add(x_23, x_113);
lean_dec(x_23);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_22);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_24);
x_116 = lean_ctor_get(x_18, 0);
lean_inc(x_116);
lean_dec(x_18);
x_117 = l_Lean_Compiler_LCNF_Arg_toExpr(x_112);
x_118 = lean_ctor_get(x_21, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_21, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_120 = x_21;
} else {
 lean_dec_ref(x_21);
 x_120 = lean_box(0);
}
x_121 = lean_array_get_size(x_119);
x_122 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_116);
x_123 = 32;
x_124 = lean_uint64_shift_right(x_122, x_123);
x_125 = lean_uint64_xor(x_122, x_124);
x_126 = 16;
x_127 = lean_uint64_shift_right(x_125, x_126);
x_128 = lean_uint64_xor(x_125, x_127);
x_129 = lean_uint64_to_usize(x_128);
x_130 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_131 = 1;
x_132 = lean_usize_sub(x_130, x_131);
x_133 = lean_usize_land(x_129, x_132);
x_134 = lean_array_uget(x_119, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_116, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_nat_add(x_118, x_113);
lean_dec(x_118);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_116);
lean_ctor_set(x_137, 1, x_117);
lean_ctor_set(x_137, 2, x_134);
x_138 = lean_array_uset(x_119, x_133, x_137);
x_139 = lean_unsigned_to_nat(4u);
x_140 = lean_nat_mul(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; size_t x_147; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_138);
if (lean_is_scalar(x_120)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_120;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_7, 1, x_146);
lean_ctor_set(x_7, 0, x_115);
x_147 = lean_usize_add(x_6, x_131);
x_6 = x_147;
goto _start;
}
else
{
lean_object* x_149; size_t x_150; 
if (lean_is_scalar(x_120)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_120;
}
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_138);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_115);
x_150 = lean_usize_add(x_6, x_131);
x_6 = x_150;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; size_t x_156; 
lean_inc(x_2);
x_152 = lean_array_uset(x_119, x_133, x_2);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_116, x_117, x_134);
x_154 = lean_array_uset(x_152, x_133, x_153);
if (lean_is_scalar(x_120)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_120;
}
lean_ctor_set(x_155, 0, x_118);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_7, 1, x_155);
lean_ctor_set(x_7, 0, x_115);
x_156 = lean_usize_add(x_6, x_131);
x_6 = x_156;
goto _start;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_7, 0);
x_159 = lean_ctor_get(x_7, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_7);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_nat_dec_lt(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_18);
lean_dec(x_2);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_15);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; lean_object* x_189; uint8_t x_190; 
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
x_167 = lean_array_fget(x_160, x_161);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_add(x_161, x_168);
lean_dec(x_161);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_160);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_162);
x_171 = lean_ctor_get(x_18, 0);
lean_inc(x_171);
lean_dec(x_18);
x_172 = l_Lean_Compiler_LCNF_Arg_toExpr(x_167);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
 x_175 = lean_box(0);
}
x_176 = lean_array_get_size(x_174);
x_177 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_171);
x_178 = 32;
x_179 = lean_uint64_shift_right(x_177, x_178);
x_180 = lean_uint64_xor(x_177, x_179);
x_181 = 16;
x_182 = lean_uint64_shift_right(x_180, x_181);
x_183 = lean_uint64_xor(x_180, x_182);
x_184 = lean_uint64_to_usize(x_183);
x_185 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_186 = 1;
x_187 = lean_usize_sub(x_185, x_186);
x_188 = lean_usize_land(x_184, x_187);
x_189 = lean_array_uget(x_174, x_188);
x_190 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_171, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_191 = lean_nat_add(x_173, x_168);
lean_dec(x_173);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_171);
lean_ctor_set(x_192, 1, x_172);
lean_ctor_set(x_192, 2, x_189);
x_193 = lean_array_uset(x_174, x_188, x_192);
x_194 = lean_unsigned_to_nat(4u);
x_195 = lean_nat_mul(x_191, x_194);
x_196 = lean_unsigned_to_nat(3u);
x_197 = lean_nat_div(x_195, x_196);
lean_dec(x_195);
x_198 = lean_array_get_size(x_193);
x_199 = lean_nat_dec_le(x_197, x_198);
lean_dec(x_198);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; size_t x_203; 
x_200 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_193);
if (lean_is_scalar(x_175)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_175;
}
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_170);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_usize_add(x_6, x_186);
x_6 = x_203;
x_7 = x_202;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; size_t x_207; 
if (lean_is_scalar(x_175)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_175;
}
lean_ctor_set(x_205, 0, x_191);
lean_ctor_set(x_205, 1, x_193);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_170);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_usize_add(x_6, x_186);
x_6 = x_207;
x_7 = x_206;
goto _start;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; 
lean_inc(x_2);
x_209 = lean_array_uset(x_174, x_188, x_2);
x_210 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_171, x_172, x_189);
x_211 = lean_array_uset(x_209, x_188, x_210);
if (lean_is_scalar(x_175)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_175;
}
lean_ctor_set(x_212, 0, x_173);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_170);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_usize_add(x_6, x_186);
x_6 = x_214;
x_7 = x_213;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_toSubarray___rarg(x_3, x_15, x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_1);
x_21 = 0;
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_13, x_17, x_1, x_20, x_21, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_Code_internalize(x_2, x_25, x_8, x_9, x_10, x_11, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_st_ref_take(x_4, x_10);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_2);
x_125 = l_Lean_Expr_fvar___override(x_2);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; size_t x_137; size_t x_138; size_t x_139; size_t x_140; size_t x_141; lean_object* x_142; uint8_t x_143; 
x_127 = lean_ctor_get(x_124, 0);
x_128 = lean_ctor_get(x_124, 1);
x_129 = lean_array_get_size(x_128);
x_130 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_131 = 32;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = 16;
x_135 = lean_uint64_shift_right(x_133, x_134);
x_136 = lean_uint64_xor(x_133, x_135);
x_137 = lean_uint64_to_usize(x_136);
x_138 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_139 = 1;
x_140 = lean_usize_sub(x_138, x_139);
x_141 = lean_usize_land(x_137, x_140);
x_142 = lean_array_uget(x_128, x_141);
x_143 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_127, x_144);
lean_dec(x_127);
lean_inc(x_1);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_125);
lean_ctor_set(x_146, 2, x_142);
x_147 = lean_array_uset(x_128, x_141, x_146);
x_148 = lean_unsigned_to_nat(4u);
x_149 = lean_nat_mul(x_145, x_148);
x_150 = lean_unsigned_to_nat(3u);
x_151 = lean_nat_div(x_149, x_150);
lean_dec(x_149);
x_152 = lean_array_get_size(x_147);
x_153 = lean_nat_dec_le(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_147);
lean_ctor_set(x_124, 1, x_154);
lean_ctor_set(x_124, 0, x_145);
x_155 = lean_st_ref_set(x_4, x_121, x_122);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_11 = x_156;
goto block_119;
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_ctor_set(x_124, 1, x_147);
lean_ctor_set(x_124, 0, x_145);
x_157 = lean_st_ref_set(x_4, x_121, x_122);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_11 = x_158;
goto block_119;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_box(0);
x_160 = lean_array_uset(x_128, x_141, x_159);
lean_inc(x_1);
x_161 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_1, x_125, x_142);
x_162 = lean_array_uset(x_160, x_141, x_161);
lean_ctor_set(x_124, 1, x_162);
x_163 = lean_st_ref_set(x_4, x_121, x_122);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_11 = x_164;
goto block_119;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; size_t x_175; size_t x_176; size_t x_177; size_t x_178; size_t x_179; lean_object* x_180; uint8_t x_181; 
x_165 = lean_ctor_get(x_124, 0);
x_166 = lean_ctor_get(x_124, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_124);
x_167 = lean_array_get_size(x_166);
x_168 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_169 = 32;
x_170 = lean_uint64_shift_right(x_168, x_169);
x_171 = lean_uint64_xor(x_168, x_170);
x_172 = 16;
x_173 = lean_uint64_shift_right(x_171, x_172);
x_174 = lean_uint64_xor(x_171, x_173);
x_175 = lean_uint64_to_usize(x_174);
x_176 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_177 = 1;
x_178 = lean_usize_sub(x_176, x_177);
x_179 = lean_usize_land(x_175, x_178);
x_180 = lean_array_uget(x_166, x_179);
x_181 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_add(x_165, x_182);
lean_dec(x_165);
lean_inc(x_1);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_1);
lean_ctor_set(x_184, 1, x_125);
lean_ctor_set(x_184, 2, x_180);
x_185 = lean_array_uset(x_166, x_179, x_184);
x_186 = lean_unsigned_to_nat(4u);
x_187 = lean_nat_mul(x_183, x_186);
x_188 = lean_unsigned_to_nat(3u);
x_189 = lean_nat_div(x_187, x_188);
lean_dec(x_187);
x_190 = lean_array_get_size(x_185);
x_191 = lean_nat_dec_le(x_189, x_190);
lean_dec(x_190);
lean_dec(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_185);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_183);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_121, 0, x_193);
x_194 = lean_st_ref_set(x_4, x_121, x_122);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_11 = x_195;
goto block_119;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_183);
lean_ctor_set(x_196, 1, x_185);
lean_ctor_set(x_121, 0, x_196);
x_197 = lean_st_ref_set(x_4, x_121, x_122);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_11 = x_198;
goto block_119;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_199 = lean_box(0);
x_200 = lean_array_uset(x_166, x_179, x_199);
lean_inc(x_1);
x_201 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_1, x_125, x_180);
x_202 = lean_array_uset(x_200, x_179, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_165);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_121, 0, x_203);
x_204 = lean_st_ref_set(x_4, x_121, x_122);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_11 = x_205;
goto block_119;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; size_t x_226; size_t x_227; size_t x_228; size_t x_229; size_t x_230; lean_object* x_231; uint8_t x_232; 
x_206 = lean_ctor_get(x_121, 0);
x_207 = lean_ctor_get(x_121, 1);
x_208 = lean_ctor_get(x_121, 2);
x_209 = lean_ctor_get(x_121, 3);
x_210 = lean_ctor_get_uint8(x_121, sizeof(void*)*7);
x_211 = lean_ctor_get(x_121, 4);
x_212 = lean_ctor_get(x_121, 5);
x_213 = lean_ctor_get(x_121, 6);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_121);
lean_inc(x_2);
x_214 = l_Lean_Expr_fvar___override(x_2);
x_215 = lean_ctor_get(x_206, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_206, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_217 = x_206;
} else {
 lean_dec_ref(x_206);
 x_217 = lean_box(0);
}
x_218 = lean_array_get_size(x_216);
x_219 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_220 = 32;
x_221 = lean_uint64_shift_right(x_219, x_220);
x_222 = lean_uint64_xor(x_219, x_221);
x_223 = 16;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_xor(x_222, x_224);
x_226 = lean_uint64_to_usize(x_225);
x_227 = lean_usize_of_nat(x_218);
lean_dec(x_218);
x_228 = 1;
x_229 = lean_usize_sub(x_227, x_228);
x_230 = lean_usize_land(x_226, x_229);
x_231 = lean_array_uget(x_216, x_230);
x_232 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_1, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_215, x_233);
lean_dec(x_215);
lean_inc(x_1);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_214);
lean_ctor_set(x_235, 2, x_231);
x_236 = lean_array_uset(x_216, x_230, x_235);
x_237 = lean_unsigned_to_nat(4u);
x_238 = lean_nat_mul(x_234, x_237);
x_239 = lean_unsigned_to_nat(3u);
x_240 = lean_nat_div(x_238, x_239);
lean_dec(x_238);
x_241 = lean_array_get_size(x_236);
x_242 = lean_nat_dec_le(x_240, x_241);
lean_dec(x_241);
lean_dec(x_240);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_236);
if (lean_is_scalar(x_217)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_217;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_207);
lean_ctor_set(x_245, 2, x_208);
lean_ctor_set(x_245, 3, x_209);
lean_ctor_set(x_245, 4, x_211);
lean_ctor_set(x_245, 5, x_212);
lean_ctor_set(x_245, 6, x_213);
lean_ctor_set_uint8(x_245, sizeof(void*)*7, x_210);
x_246 = lean_st_ref_set(x_4, x_245, x_122);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_11 = x_247;
goto block_119;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
if (lean_is_scalar(x_217)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_217;
}
lean_ctor_set(x_248, 0, x_234);
lean_ctor_set(x_248, 1, x_236);
x_249 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_207);
lean_ctor_set(x_249, 2, x_208);
lean_ctor_set(x_249, 3, x_209);
lean_ctor_set(x_249, 4, x_211);
lean_ctor_set(x_249, 5, x_212);
lean_ctor_set(x_249, 6, x_213);
lean_ctor_set_uint8(x_249, sizeof(void*)*7, x_210);
x_250 = lean_st_ref_set(x_4, x_249, x_122);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_11 = x_251;
goto block_119;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_252 = lean_box(0);
x_253 = lean_array_uset(x_216, x_230, x_252);
lean_inc(x_1);
x_254 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_1, x_214, x_231);
x_255 = lean_array_uset(x_253, x_230, x_254);
if (lean_is_scalar(x_217)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_217;
}
lean_ctor_set(x_256, 0, x_215);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_207);
lean_ctor_set(x_257, 2, x_208);
lean_ctor_set(x_257, 3, x_209);
lean_ctor_set(x_257, 4, x_211);
lean_ctor_set(x_257, 5, x_212);
lean_ctor_set(x_257, 6, x_213);
lean_ctor_set_uint8(x_257, sizeof(void*)*7, x_210);
x_258 = lean_st_ref_set(x_4, x_257, x_122);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_11 = x_259;
goto block_119;
}
}
block_119:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_getBinderName(x_1, x_6, x_7, x_8, x_9, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Name_isInternal(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_12);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_getBinderName(x_2, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Name_isInternal(x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_17);
x_23 = lean_st_ref_take(x_4, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 2);
x_28 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_27, x_2, x_14);
lean_ctor_set(x_24, 2, x_28);
x_29 = lean_st_ref_set(x_4, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
x_40 = lean_ctor_get_uint8(x_24, sizeof(void*)*7);
x_41 = lean_ctor_get(x_24, 4);
x_42 = lean_ctor_get(x_24, 5);
x_43 = lean_ctor_get(x_24, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_44 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_38, x_2, x_14);
x_45 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_41);
lean_ctor_set(x_45, 5, x_42);
lean_ctor_set(x_45, 6, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*7, x_40);
x_46 = lean_st_ref_set(x_4, x_45, x_25);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = l_Lean_Name_isInternal(x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_14);
lean_dec(x_2);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_st_ref_take(x_4, x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_57, sizeof(void*)*7);
x_64 = lean_ctor_get(x_57, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 6);
lean_inc(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_61, x_2, x_14);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 7, 1);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*7, x_63);
x_70 = lean_st_ref_set(x_4, x_69, x_58);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_14);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_17);
if (x_75 == 0)
{
return x_17;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_17, 0);
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_17);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_14);
lean_dec(x_2);
x_79 = lean_box(0);
lean_ctor_set(x_12, 0, x_79);
return x_12;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_12, 0);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_12);
x_82 = l_Lean_Name_isInternal(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
lean_inc(x_2);
x_83 = l_Lean_Compiler_LCNF_getBinderName(x_2, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Name_isInternal(x_84);
lean_dec(x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_80);
lean_dec(x_2);
x_88 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_86);
x_90 = lean_st_ref_take(x_4, x_85);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_91, sizeof(void*)*7);
x_98 = lean_ctor_get(x_91, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 5);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 6);
lean_inc(x_100);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 lean_ctor_release(x_91, 6);
 x_101 = x_91;
} else {
 lean_dec_ref(x_91);
 x_101 = lean_box(0);
}
x_102 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_95, x_2, x_80);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 7, 1);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_94);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_96);
lean_ctor_set(x_103, 4, x_98);
lean_ctor_set(x_103, 5, x_99);
lean_ctor_set(x_103, 6, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*7, x_97);
x_104 = lean_st_ref_set(x_4, x_103, x_92);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_80);
lean_dec(x_2);
x_109 = lean_ctor_get(x_83, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_83, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_111 = x_83;
} else {
 lean_dec_ref(x_83);
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
lean_object* x_113; lean_object* x_114; 
lean_dec(x_80);
lean_dec(x_2);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_81);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_12);
if (x_115 == 0)
{
return x_12;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_12, 0);
x_117 = lean_ctor_get(x_12, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_12);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__1);
l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__2);
l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___closed__3);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__2);
l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__2___closed__3);
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
l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__1);
l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___closed__2);
l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__2___at_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___spec__3___closed__1);
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
