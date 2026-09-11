// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: public import Lean.Compiler.LCNF.Simp.InlineCandidate public import Lean.Compiler.LCNF.Simp.InlineProj public import Lean.Compiler.LCNF.Simp.Used public import Lean.Compiler.LCNF.Simp.DefaultAlt public import Lean.Compiler.LCNF.Simp.SimpValue public import Lean.Compiler.LCNF.Simp.ConstantFold
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
static const lean_array_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LCNF simp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0(void){
_start:
{
uint8_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 0;
v___x_2_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* v_c_3_){
_start:
{
switch(lean_obj_tag(v_c_3_))
{
case 0:
{
lean_object* v_k_4_; 
v_k_4_ = lean_ctor_get(v_c_3_, 1);
v_c_3_ = v_k_4_;
goto _start;
}
case 1:
{
lean_object* v_k_6_; 
v_k_6_ = lean_ctor_get(v_c_3_, 1);
v_c_3_ = v_k_6_;
goto _start;
}
case 4:
{
lean_object* v_cases_8_; lean_object* v_alts_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_cases_8_ = lean_ctor_get(v_c_3_, 0);
v_alts_9_ = lean_ctor_get(v_cases_8_, 3);
v___x_10_ = lean_array_get_size(v_alts_9_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_dec_eq(v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_array_get_borrowed(v___x_13_, v_alts_9_, v___x_14_);
switch(lean_obj_tag(v___x_15_))
{
case 0:
{
lean_object* v_code_16_; 
v_code_16_ = lean_ctor_get(v___x_15_, 2);
v_c_3_ = v_code_16_;
goto _start;
}
case 1:
{
lean_object* v_code_18_; 
v_code_18_ = lean_ctor_get(v___x_15_, 1);
v_c_3_ = v_code_18_;
goto _start;
}
default: 
{
lean_object* v_code_20_; 
v_code_20_ = lean_ctor_get(v___x_15_, 0);
v_c_3_ = v_code_20_;
goto _start;
}
}
}
}
case 5:
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
default: 
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* v_c_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_24_);
lean_dec_ref(v_c_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* v_c_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* v_c_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(v_c_29_);
lean_dec_ref(v_c_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* v_a_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
else
{
lean_object* v_key_35_; lean_object* v_tail_36_; uint8_t v___x_37_; 
v_key_35_ = lean_ctor_get(v_x_33_, 0);
v_tail_36_ = lean_ctor_get(v_x_33_, 2);
v___x_37_ = l_Lean_instBEqFVarId_beq(v_key_35_, v_a_32_);
if (v___x_37_ == 0)
{
v_x_33_ = v_tail_36_;
goto _start;
}
else
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* v_a_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_39_, v_x_40_);
lean_dec(v_x_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
return v_x_43_;
}
else
{
lean_object* v_key_45_; lean_object* v_value_46_; lean_object* v_tail_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_70_; 
v_key_45_ = lean_ctor_get(v_x_44_, 0);
v_value_46_ = lean_ctor_get(v_x_44_, 1);
v_tail_47_ = lean_ctor_get(v_x_44_, 2);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_70_ == 0)
{
v___x_49_ = v_x_44_;
v_isShared_50_ = v_isSharedCheck_70_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_tail_47_);
lean_inc(v_value_46_);
lean_inc(v_key_45_);
lean_dec(v_x_44_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_70_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; uint64_t v_fold_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_51_ = lean_array_get_size(v_x_43_);
v___x_52_ = l_Lean_instHashableFVarId_hash(v_key_45_);
v___x_53_ = 32ULL;
v___x_54_ = lean_uint64_shift_right(v___x_52_, v___x_53_);
v_fold_55_ = lean_uint64_xor(v___x_52_, v___x_54_);
v___x_56_ = 16ULL;
v___x_57_ = lean_uint64_shift_right(v_fold_55_, v___x_56_);
v___x_58_ = lean_uint64_xor(v_fold_55_, v___x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = lean_usize_of_nat(v___x_51_);
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_sub(v___x_60_, v___x_61_);
v___x_63_ = lean_usize_land(v___x_59_, v___x_62_);
v___x_64_ = lean_array_uget_borrowed(v_x_43_, v___x_63_);
lean_inc(v___x_64_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_64_);
v___x_66_ = v___x_49_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_key_45_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_value_46_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v___x_64_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_array_uset(v_x_43_, v___x_63_, v___x_66_);
v_x_43_ = v___x_67_;
v_x_44_ = v_tail_47_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object* v_i_71_, lean_object* v_source_72_, lean_object* v_target_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_array_get_size(v_source_72_);
v___x_75_ = lean_nat_dec_lt(v_i_71_, v___x_74_);
if (v___x_75_ == 0)
{
lean_dec_ref(v_source_72_);
lean_dec(v_i_71_);
return v_target_73_;
}
else
{
lean_object* v_es_76_; lean_object* v___x_77_; lean_object* v_source_78_; lean_object* v_target_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_es_76_ = lean_array_fget(v_source_72_, v_i_71_);
v___x_77_ = lean_box(0);
v_source_78_ = lean_array_fset(v_source_72_, v_i_71_, v___x_77_);
v_target_79_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_target_73_, v_es_76_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_i_71_, v___x_80_);
lean_dec(v_i_71_);
v_i_71_ = v___x_81_;
v_source_72_ = v_source_78_;
v_target_73_ = v_target_79_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* v_data_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_nbuckets_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_84_ = lean_array_get_size(v_data_83_);
v___x_85_ = lean_unsigned_to_nat(2u);
v_nbuckets_86_ = lean_nat_mul(v___x_84_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_box(0);
v___x_89_ = lean_mk_array(v_nbuckets_86_, v___x_88_);
v___x_90_ = lean_array_propagate_mark(v_data_83_, v___x_89_);
v___x_91_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_87_, v_data_83_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object* v_a_92_, lean_object* v_b_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_dec(v_b_93_);
lean_dec(v_a_92_);
return v_x_94_;
}
else
{
lean_object* v_key_95_; lean_object* v_value_96_; lean_object* v_tail_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_109_; 
v_key_95_ = lean_ctor_get(v_x_94_, 0);
v_value_96_ = lean_ctor_get(v_x_94_, 1);
v_tail_97_ = lean_ctor_get(v_x_94_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_109_ == 0)
{
v___x_99_ = v_x_94_;
v_isShared_100_ = v_isSharedCheck_109_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_tail_97_);
lean_inc(v_value_96_);
lean_inc(v_key_95_);
lean_dec(v_x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_109_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_instBEqFVarId_beq(v_key_95_, v_a_92_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_92_, v_b_93_, v_tail_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 2, v___x_102_);
v___x_104_ = v___x_99_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_key_95_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_value_96_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
lean_dec(v_value_96_);
lean_dec(v_key_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_b_93_);
lean_ctor_set(v___x_99_, 0, v_a_92_);
v___x_107_ = v___x_99_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_92_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_b_93_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_tail_97_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* v_m_110_, lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_size_113_; lean_object* v_buckets_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_157_; 
v_size_113_ = lean_ctor_get(v_m_110_, 0);
v_buckets_114_ = lean_ctor_get(v_m_110_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_m_110_);
if (v_isSharedCheck_157_ == 0)
{
v___x_116_ = v_m_110_;
v_isShared_117_ = v_isSharedCheck_157_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_buckets_114_);
lean_inc(v_size_113_);
lean_dec(v_m_110_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_157_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v_bkt_131_; uint8_t v___x_132_; 
v___x_118_ = lean_array_get_size(v_buckets_114_);
v___x_119_ = l_Lean_instHashableFVarId_hash(v_a_111_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_118_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v_bkt_131_ = lean_array_uget_borrowed(v_buckets_114_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_111_, v_bkt_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v_size_x27_134_; lean_object* v___x_135_; lean_object* v_buckets_x27_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v_size_x27_134_ = lean_nat_add(v_size_113_, v___x_133_);
lean_dec(v_size_113_);
lean_inc(v_bkt_131_);
v___x_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_135_, 0, v_a_111_);
lean_ctor_set(v___x_135_, 1, v_b_112_);
lean_ctor_set(v___x_135_, 2, v_bkt_131_);
v_buckets_x27_136_ = lean_array_uset(v_buckets_114_, v___x_130_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(4u);
v___x_138_ = lean_nat_mul(v_size_x27_134_, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(3u);
v___x_140_ = lean_nat_div(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_array_get_size(v_buckets_x27_136_);
v___x_142_ = lean_nat_dec_le(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
if (v___x_142_ == 0)
{
lean_object* v_val_143_; lean_object* v___x_145_; 
v_val_143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_buckets_x27_136_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_val_143_);
lean_ctor_set(v___x_116_, 0, v_size_x27_134_);
v___x_145_ = v___x_116_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_size_x27_134_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_val_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v___x_148_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_buckets_x27_136_);
lean_ctor_set(v___x_116_, 0, v_size_x27_134_);
v___x_148_ = v___x_116_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_size_x27_134_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_buckets_x27_136_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v___x_150_; lean_object* v_buckets_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_inc(v_bkt_131_);
v___x_150_ = lean_box(0);
v_buckets_x27_151_ = lean_array_uset(v_buckets_114_, v___x_130_, v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_111_, v_b_112_, v_bkt_131_);
v___x_153_ = lean_array_uset(v_buckets_x27_151_, v___x_130_, v___x_152_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_153_);
v___x_155_ = v___x_116_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_113_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* v_as_158_, size_t v_sz_159_, size_t v_i_160_, lean_object* v_b_161_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_usize_dec_lt(v_i_160_, v_sz_159_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v_b_161_);
return v___x_164_;
}
else
{
lean_object* v_snd_165_; lean_object* v_fst_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_200_; 
v_snd_165_ = lean_ctor_get(v_b_161_, 1);
v_fst_166_ = lean_ctor_get(v_b_161_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_b_161_);
if (v_isSharedCheck_200_ == 0)
{
v___x_168_ = v_b_161_;
v_isShared_169_ = v_isSharedCheck_200_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_snd_165_);
lean_inc(v_fst_166_);
lean_dec(v_b_161_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_200_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_array_170_; lean_object* v_start_171_; lean_object* v_stop_172_; uint8_t v___x_173_; 
v_array_170_ = lean_ctor_get(v_snd_165_, 0);
v_start_171_ = lean_ctor_get(v_snd_165_, 1);
v_stop_172_ = lean_ctor_get(v_snd_165_, 2);
v___x_173_ = lean_nat_dec_lt(v_start_171_, v_stop_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_175_; 
if (v_isShared_169_ == 0)
{
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_fst_166_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_snd_165_);
v___x_175_ = v_reuseFailAlloc_177_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
else
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_196_; 
lean_inc(v_stop_172_);
lean_inc(v_start_171_);
lean_inc_ref(v_array_170_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_snd_165_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; lean_object* v_unused_199_; 
v_unused_197_ = lean_ctor_get(v_snd_165_, 2);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_snd_165_, 1);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_snd_165_, 0);
lean_dec(v_unused_199_);
v___x_179_ = v_snd_165_;
v_isShared_180_ = v_isSharedCheck_196_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_snd_165_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_196_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_a_181_; lean_object* v_fvarId_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v_a_181_ = lean_array_uget_borrowed(v_as_158_, v_i_160_);
v_fvarId_182_ = lean_ctor_get(v_a_181_, 0);
v___x_183_ = lean_array_fget(v_array_170_, v_start_171_);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_start_171_, v___x_184_);
lean_dec(v_start_171_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_185_);
v___x_187_ = v___x_179_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_array_170_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_stop_172_);
v___x_187_ = v_reuseFailAlloc_195_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_fvarId_182_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_166_, v_fvarId_182_, v___x_183_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_187_);
lean_ctor_set(v___x_168_, 0, v___x_188_);
v___x_190_ = v___x_168_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_187_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_160_, v___x_191_);
v_i_160_ = v___x_192_;
v_b_161_ = v___x_190_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* v_as_201_, lean_object* v_sz_202_, lean_object* v_i_203_, lean_object* v_b_204_, lean_object* v___y_205_){
_start:
{
size_t v_sz_boxed_206_; size_t v_i_boxed_207_; lean_object* v_res_208_; 
v_sz_boxed_206_ = lean_unbox_usize(v_sz_202_);
lean_dec(v_sz_202_);
v_i_boxed_207_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_201_, v_sz_boxed_206_, v_i_boxed_207_, v_b_204_);
lean_dec_ref(v_as_201_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* v_a_209_, lean_object* v_b_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_array_216_; lean_object* v_start_217_; lean_object* v_stop_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_268_; 
v_array_216_ = lean_ctor_get(v_a_209_, 0);
v_start_217_ = lean_ctor_get(v_a_209_, 1);
v_stop_218_ = lean_ctor_get(v_a_209_, 2);
v_isSharedCheck_268_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_268_ == 0)
{
v___x_220_ = v_a_209_;
v_isShared_221_ = v_isSharedCheck_268_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_stop_218_);
lean_inc(v_start_217_);
lean_inc(v_array_216_);
lean_dec(v_a_209_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_268_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; 
v___x_222_ = lean_nat_dec_lt(v_start_217_, v_stop_218_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_del_object(v___x_220_);
lean_dec(v_stop_218_);
lean_dec(v_start_217_);
lean_dec_ref(v_array_216_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_b_210_);
return v___x_223_;
}
else
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_267_; 
v_fst_224_ = lean_ctor_get(v_b_210_, 0);
v_snd_225_ = lean_ctor_get(v_b_210_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_b_210_);
if (v_isSharedCheck_267_ == 0)
{
v___x_227_ = v_b_210_;
v_isShared_228_ = v_isSharedCheck_267_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_snd_225_);
lean_inc(v_fst_224_);
lean_dec(v_b_210_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_267_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v_fvarId_230_; lean_object* v_type_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_229_ = lean_array_fget_borrowed(v_array_216_, v_start_217_);
v_fvarId_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_fvarId_230_);
v_type_231_ = lean_ctor_get(v___x_229_, 2);
v___x_232_ = 0;
lean_inc_ref(v_type_231_);
v___x_233_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v___x_232_, v_type_231_, v_fst_224_, v___x_222_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; uint8_t v___x_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = 0;
v___x_236_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_232_, v_a_234_, v___x_235_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v_fvarId_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v_fvarId_238_ = lean_ctor_get(v_a_237_, 0);
lean_inc(v_fvarId_238_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_start_217_, v___x_239_);
lean_dec(v_start_217_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_240_);
v___x_242_ = v___x_220_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_array_216_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_stop_218_);
v___x_242_ = v_reuseFailAlloc_250_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_243_ = lean_array_push(v_snd_225_, v_a_237_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_fvarId_238_);
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_224_, v_fvarId_230_, v___x_244_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_243_);
lean_ctor_set(v___x_227_, 0, v___x_245_);
v___x_247_ = v___x_227_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_243_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v_a_209_ = v___x_242_;
v_b_210_ = v___x_247_;
goto _start;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_fvarId_230_);
lean_del_object(v___x_227_);
lean_dec(v_snd_225_);
lean_dec(v_fst_224_);
lean_del_object(v___x_220_);
lean_dec(v_stop_218_);
lean_dec(v_start_217_);
lean_dec_ref(v_array_216_);
v_a_251_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_236_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_236_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_fvarId_230_);
lean_del_object(v___x_227_);
lean_dec(v_snd_225_);
lean_dec(v_fst_224_);
lean_del_object(v___x_220_);
lean_dec(v_stop_218_);
lean_dec(v_start_217_);
lean_dec_ref(v_array_216_);
v_a_259_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_233_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_233_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_269_, v_b_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
v___x_278_ = lean_unsigned_to_nat(16u);
v___x_279_ = lean_mk_array(v___x_278_, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_subst_282_; 
v___x_280_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
v___x_281_ = lean_unsigned_to_nat(0u);
v_subst_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_subst_282_, 0, v___x_281_);
lean_ctor_set(v_subst_282_, 1, v___x_280_);
return v_subst_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* v_info_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_params_297_; lean_object* v_value_298_; lean_object* v_args_299_; lean_object* v___x_300_; lean_object* v_subst_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; size_t v_sz_305_; size_t v___x_306_; lean_object* v___x_307_; 
v_params_297_ = lean_ctor_get(v_info_288_, 0);
lean_inc_ref(v_params_297_);
v_value_298_ = lean_ctor_get(v_info_288_, 1);
lean_inc_ref(v_value_298_);
v_args_299_ = lean_ctor_get(v_info_288_, 3);
lean_inc_ref(v_args_299_);
lean_dec_ref(v_info_288_);
v___x_300_ = lean_unsigned_to_nat(0u);
v_subst_301_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
v___x_302_ = lean_array_get_size(v_args_299_);
v___x_303_ = l_Array_toSubarray___redArg(v_args_299_, v___x_300_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_subst_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v_sz_305_ = lean_array_size(v_params_297_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_params_297_, v_sz_305_, v___x_306_, v___x_304_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_fst_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_358_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_fst_309_ = lean_ctor_get(v_a_308_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_a_308_, 1);
lean_dec(v_unused_359_);
v___x_311_ = v_a_308_;
v_isShared_312_ = v_isSharedCheck_358_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_fst_309_);
lean_dec(v_a_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_358_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v_lower_315_; lean_object* v_upper_316_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_313_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2));
v___x_356_ = lean_array_get_size(v_params_297_);
v___x_357_ = lean_nat_dec_le(v___x_302_, v___x_300_);
if (v___x_357_ == 0)
{
v_lower_315_ = v___x_302_;
v_upper_316_ = v___x_356_;
goto v___jp_314_;
}
else
{
v_lower_315_ = v___x_300_;
v_upper_316_ = v___x_356_;
goto v___jp_314_;
}
v___jp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l_Array_toSubarray___redArg(v_params_297_, v_lower_315_, v_upper_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_313_);
v___x_319_ = v___x_311_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_313_);
v___x_319_ = v_reuseFailAlloc_355_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v___x_317_, v___x_319_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; uint8_t v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v_fst_322_ = lean_ctor_get(v_a_321_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v_a_321_, 1);
lean_inc(v_snd_323_);
lean_dec(v_a_321_);
v___x_324_ = 0;
v___x_325_ = 0;
v___x_326_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_324_, v_value_298_, v_fst_322_, v___x_325_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_n(v_a_327_, 2);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_327_, v___x_325_, v_a_290_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_330_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_snd_323_, v_a_327_, v___x_329_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_330_;
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_a_327_);
lean_dec(v_snd_323_);
v_a_331_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_328_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_snd_323_);
v_a_339_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_326_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_326_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v_value_298_);
v_a_347_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_320_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_320_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_value_298_);
lean_dec_ref(v_params_297_);
v_a_360_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_307_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_307_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* v_info_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_info_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* v_00_u03b2_378_, lean_object* v_m_379_, lean_object* v_a_380_, lean_object* v_b_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_379_, v_a_380_, v_b_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* v_as_383_, size_t v_sz_384_, size_t v_i_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_383_, v_sz_384_, v_i_385_, v_b_386_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* v_as_396_, lean_object* v_sz_397_, lean_object* v_i_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_397_);
lean_dec(v_sz_397_);
v_i_boxed_409_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_396_, v_sz_boxed_408_, v_i_boxed_409_, v_b_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v_as_396_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* v_inst_411_, lean_object* v_R_412_, lean_object* v_a_413_, lean_object* v_b_414_, lean_object* v_c_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_413_, v_b_414_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* v_inst_425_, lean_object* v_R_426_, lean_object* v_a_427_, lean_object* v_b_428_, lean_object* v_c_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(v_inst_425_, v_R_426_, v_a_427_, v_b_428_, v_c_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* v_00_u03b2_439_, lean_object* v_a_440_, lean_object* v_x_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* v_00_u03b2_443_, lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_443_, v_a_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec(v_a_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* v_00_u03b2_448_, lean_object* v_data_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_data_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object* v_00_u03b2_451_, lean_object* v_a_452_, lean_object* v_b_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_452_, v_b_453_, v_x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_456_, lean_object* v_i_457_, lean_object* v_source_458_, lean_object* v_target_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v_i_457_, v_source_458_, v_target_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_x_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* v_fvarId_465_, lean_object* v_args_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
uint8_t v___x_475_; lean_object* v___x_476_; 
v___x_475_ = 0;
v___x_476_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_475_, v_fvarId_465_, v_a_471_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_541_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_541_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_541_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_541_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
if (lean_obj_tag(v_a_477_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_536_; 
lean_del_object(v___x_479_);
v_val_481_ = lean_ctor_get(v_a_477_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_536_ == 0)
{
v___x_483_ = v_a_477_;
v_isShared_484_ = v_isSharedCheck_536_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v_a_477_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_536_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_val_481_, v_a_468_, v_a_470_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_527_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_527_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_527_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_527_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint8_t v___x_490_; 
v___x_490_ = lean_unbox(v_a_486_);
lean_dec(v_a_486_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_dec_ref(v_args_466_);
v___x_491_ = lean_box(0);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_491_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_495_; 
lean_del_object(v___x_488_);
v___x_495_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_468_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_params_496_; lean_object* v_value_497_; uint8_t v___x_498_; lean_object* v___x_499_; 
lean_dec_ref_known(v___x_495_, 1);
v_params_496_ = lean_ctor_get(v_val_481_, 2);
lean_inc_ref(v_params_496_);
v_value_497_ = lean_ctor_get(v_val_481_, 4);
lean_inc_ref(v_value_497_);
lean_dec(v_val_481_);
v___x_498_ = 0;
v___x_499_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_496_, v_value_497_, v_args_466_, v___x_498_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec_ref(v_params_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_a_500_);
v___x_505_ = v___x_483_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_483_);
v_a_511_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_499_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_dec_ref(v_args_466_);
v_a_519_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_495_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_495_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_483_);
lean_dec(v_val_481_);
lean_dec_ref(v_args_466_);
v_a_528_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_485_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_485_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_a_477_);
lean_dec_ref(v_args_466_);
v___x_537_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_537_);
v___x_539_ = v___x_479_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_args_466_);
v_a_542_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_476_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_476_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* v_fvarId_550_, lean_object* v_args_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_550_, v_args_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_fvarId_550_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* v_declName_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_env_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_564_ = lean_st_ref_get(v___y_562_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_env_565_);
lean_dec(v___x_564_);
v___x_566_ = l_Lean_isInstanceReducibleCore(v_env_565_, v_declName_561_);
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_570_, v___y_571_);
lean_dec(v___y_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* v_declName_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_574_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* v_declName_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t v_sz_594_, size_t v_i_595_, lean_object* v_bs_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_597_ == 0)
{
return v_bs_596_;
}
else
{
lean_object* v_v_598_; lean_object* v_fvarId_599_; lean_object* v___x_600_; lean_object* v_bs_x27_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v_v_598_ = lean_array_uget_borrowed(v_bs_596_, v_i_595_);
v_fvarId_599_ = lean_ctor_get(v_v_598_, 0);
lean_inc(v_fvarId_599_);
v___x_600_ = lean_unsigned_to_nat(0u);
v_bs_x27_601_ = lean_array_uset(v_bs_596_, v_i_595_, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_fvarId_599_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_595_, v___x_603_);
v___x_605_ = lean_array_uset(v_bs_x27_601_, v_i_595_, v___x_602_);
v_i_595_ = v___x_604_;
v_bs_596_ = v___x_605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_bs_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_611_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_610_, v_i_boxed_611_, v_bs_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* v_letDecl_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_config_625_; uint8_t v_etaPoly_626_; 
v_config_625_ = lean_ctor_get(v_a_617_, 1);
v_etaPoly_626_ = lean_ctor_get_uint8(v_config_625_, 0);
if (v_etaPoly_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec_ref(v_letDecl_616_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v_value_629_; 
v_value_629_ = lean_ctor_get(v_letDecl_616_, 3);
lean_inc(v_value_629_);
if (lean_obj_tag(v_value_629_) == 3)
{
lean_object* v_fvarId_630_; lean_object* v_type_631_; lean_object* v_declName_632_; lean_object* v_us_633_; lean_object* v_args_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_803_; 
v_fvarId_630_ = lean_ctor_get(v_letDecl_616_, 0);
v_type_631_ = lean_ctor_get(v_letDecl_616_, 2);
v_declName_632_ = lean_ctor_get(v_value_629_, 0);
v_us_633_ = lean_ctor_get(v_value_629_, 1);
v_args_634_ = lean_ctor_get(v_value_629_, 2);
v_isSharedCheck_803_ = !lean_is_exclusive(v_value_629_);
if (v_isSharedCheck_803_ == 0)
{
v___x_636_ = v_value_629_;
v_isShared_637_ = v_isSharedCheck_803_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_args_634_);
lean_inc(v_us_633_);
lean_inc(v_declName_632_);
lean_dec(v_value_629_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_803_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v_env_639_; uint8_t v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_st_ref_get(v_a_623_);
v_env_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_env_639_);
lean_dec(v___x_638_);
v___x_640_ = 0;
lean_inc(v_declName_632_);
v___x_641_ = l_Lean_Environment_find_x3f(v_env_639_, v_declName_632_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = l_Lean_ConstantInfo_type(v_val_642_);
lean_dec(v_val_642_);
v___x_644_ = l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_643_, v_a_623_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_792_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_792_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_792_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_792_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = lean_unbox(v_a_645_);
lean_dec(v_a_645_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v___x_650_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_650_);
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_647_);
lean_inc(v_declName_632_);
v___x_654_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_632_, v_a_623_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_791_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_791_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_791_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_790_; 
v_val_659_ = lean_ctor_get(v_a_655_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_655_);
if (v_isSharedCheck_790_ == 0)
{
v___x_661_ = v_a_655_;
v_isShared_662_ = v_isSharedCheck_790_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v_a_655_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_790_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v___x_663_; 
v___x_663_ = lean_unbox(v_val_659_);
lean_dec(v_val_659_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_del_object(v___x_657_);
v___x_664_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_620_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_777_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_777_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_777_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_777_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unbox(v_a_665_);
lean_inc(v_declName_632_);
v___x_670_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_632_, v___x_669_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_768_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_768_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_768_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_768_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_a_671_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_767_; 
v_val_680_ = lean_ctor_get(v_a_671_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_a_671_);
if (v_isSharedCheck_767_ == 0)
{
v___x_682_ = v_a_671_;
v_isShared_683_ = v_isSharedCheck_767_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_a_671_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_767_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___x_685_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
lean_del_object(v___x_673_);
v___x_686_ = lean_array_get_size(v_args_634_);
v___x_687_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_680_);
lean_dec(v_val_680_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
lean_dec(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_del_object(v___x_682_);
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v___x_689_ = lean_box(0);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_689_);
v___x_691_ = v___x_667_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_693_; 
lean_del_object(v___x_667_);
lean_inc_ref(v_type_631_);
v___x_693_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_685_, v_type_631_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; size_t v_sz_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_n(v_a_694_, 2);
lean_dec_ref_known(v___x_693_, 1);
v_sz_695_ = lean_array_size(v_a_694_);
v___x_696_ = ((size_t)0ULL);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_695_, v___x_696_, v_a_694_);
v___x_698_ = l_Array_append___redArg(v_args_634_, v___x_697_);
lean_dec_ref(v___x_697_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_698_);
v___x_700_ = v___x_636_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_declName_632_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_us_633_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v___x_698_);
v___x_700_ = v_reuseFailAlloc_758_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_702_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_685_, v___x_700_, v___x_701_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v_fvarId_704_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v_fvarId_704_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_fvarId_704_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 5);
lean_ctor_set(v___x_661_, 0, v_fvarId_704_);
v___x_706_ = v___x_661_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fvarId_704_);
v___x_706_ = v_reuseFailAlloc_749_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_a_703_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_709_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_694_, v___x_707_, v___x_708_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_fvarId_711_; lean_object* v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_fvarId_711_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_fvarId_711_);
lean_inc(v_fvarId_630_);
v___x_712_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_630_, v_fvarId_711_, v_a_618_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; 
lean_dec_ref_known(v___x_712_, 1);
v___x_713_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_616_, v_a_618_, v_a_621_);
lean_dec_ref(v_letDecl_616_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_724_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_a_710_);
v___x_718_ = v___x_682_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_710_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_718_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_710_);
lean_del_object(v___x_682_);
v_a_725_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_713_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_713_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_a_710_);
lean_del_object(v___x_682_);
lean_dec_ref(v_letDecl_616_);
v_a_733_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_712_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_712_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_del_object(v___x_682_);
lean_dec_ref(v_letDecl_616_);
v_a_741_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_709_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_709_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_694_);
lean_del_object(v___x_682_);
lean_del_object(v___x_661_);
lean_dec_ref(v_letDecl_616_);
v_a_750_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_702_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_702_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_del_object(v___x_682_);
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v_a_759_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_693_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_693_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
else
{
lean_del_object(v___x_682_);
lean_dec(v_val_680_);
lean_del_object(v___x_667_);
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
goto v___jp_675_;
}
}
}
else
{
lean_dec(v_a_671_);
lean_del_object(v___x_667_);
lean_dec(v_a_665_);
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_676_);
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_del_object(v___x_667_);
lean_dec(v_a_665_);
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v_a_769_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_670_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_670_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v_a_778_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_664_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_664_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_del_object(v___x_661_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v___x_786_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_786_);
v___x_788_ = v___x_657_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v_a_793_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_644_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_644_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_641_);
lean_del_object(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec(v_us_633_);
lean_dec(v_declName_632_);
lean_dec_ref(v_letDecl_616_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v_value_629_);
lean_dec_ref(v_letDecl_616_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* v_letDecl_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t v___x_816_, size_t v_sz_817_, size_t v_i_818_, lean_object* v_bs_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_817_, v_i_818_, v_bs_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* v___x_821_, lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_bs_824_){
_start:
{
uint8_t v___x_23076__boxed_825_; size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v___x_23076__boxed_825_ = lean_unbox(v___x_821_);
v_sz_boxed_826_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_827_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_23076__boxed_825_, v_sz_boxed_826_, v_i_boxed_827_, v_bs_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* v_c_829_, lean_object* v_fvarId_830_, lean_object* v_a_831_){
_start:
{
if (lean_obj_tag(v_c_829_) == 5)
{
lean_object* v_fvarId_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_855_; 
v_fvarId_833_ = lean_ctor_get(v_c_829_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_c_829_);
if (v_isSharedCheck_855_ == 0)
{
v___x_835_ = v_c_829_;
v_isShared_836_ = v_isSharedCheck_855_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_fvarId_833_);
lean_dec(v_c_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_855_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v_subst_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_837_ = lean_st_ref_get(v_a_831_);
v_subst_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_subst_838_);
lean_dec(v___x_837_);
v___x_839_ = 0;
v___x_840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_838_, v_fvarId_833_, v___x_839_);
lean_dec_ref(v_subst_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_fvarId_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_835_);
v_fvarId_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_fvarId_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_845_ = l_Lean_instBEqFVarId_beq(v_fvarId_841_, v_fvarId_830_);
lean_dec(v_fvarId_841_);
v___x_846_ = lean_box(v___x_845_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_box(v___x_839_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
lean_ctor_set(v___x_835_, 0, v___x_851_);
v___x_853_ = v___x_835_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_c_829_);
v___x_856_ = 0;
v___x_857_ = lean_box(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* v_c_859_, lean_object* v_fvarId_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_859_, v_fvarId_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec(v_fvarId_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* v_c_864_, lean_object* v_fvarId_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_864_, v_fvarId_865_, v_a_867_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* v_c_875_, lean_object* v_fvarId_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_875_, v_fvarId_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_fvarId_876_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* v_value_886_){
_start:
{
if (lean_obj_tag(v_value_886_) == 4)
{
lean_object* v_fvarId_891_; lean_object* v_args_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_fvarId_891_ = lean_ctor_get(v_value_886_, 0);
v_args_892_ = lean_ctor_get(v_value_886_, 1);
v___x_893_ = lean_array_get_size(v_args_892_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_eq(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
goto v___jp_888_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_inc(v_fvarId_891_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_fvarId_891_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
else
{
goto v___jp_888_;
}
v___jp_888_:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* v_value_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_898_);
lean_dec(v_value_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* v_value_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_901_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* v_value_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_value_911_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* v_a_921_, lean_object* v___x_922_, lean_object* v_fvarId_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_fvarId_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_fvarId_929_ = lean_ctor_get(v_a_921_, 0);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_fvarId_923_);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_922_);
v___x_932_ = lean_array_push(v___x_931_, v___x_930_);
lean_inc(v_fvarId_929_);
v___x_933_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_933_, 0, v_fvarId_929_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* v_a_935_, lean_object* v___x_936_, lean_object* v_fvarId_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_935_, v___x_936_, v_fvarId_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___x_936_);
lean_dec_ref(v_a_935_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t v_pu_944_, uint8_t v_t_945_, lean_object* v_args_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_subst_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_949_ = lean_st_ref_get(v___y_947_);
v_subst_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_subst_950_);
lean_dec(v___x_949_);
v___x_951_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_944_, v_subst_950_, v_args_946_, v_t_945_);
lean_dec_ref(v_subst_950_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* v_pu_953_, lean_object* v_t_954_, lean_object* v_args_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v_pu_boxed_958_; uint8_t v_t_boxed_959_; lean_object* v_res_960_; 
v_pu_boxed_958_ = lean_unbox(v_pu_953_);
v_t_boxed_959_ = lean_unbox(v_t_954_);
v_res_960_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_boxed_958_, v_t_boxed_959_, v_args_955_, v___y_956_);
lean_dec(v___y_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* v_as_961_, size_t v_i_962_, size_t v_stop_963_, lean_object* v_b_964_, lean_object* v___y_965_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_eq(v_i_962_, v_stop_963_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_array_uget_borrowed(v_as_961_, v_i_962_);
lean_inc(v___x_968_);
v___x_969_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_968_, v___y_965_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; size_t v___x_971_; size_t v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_add(v_i_962_, v___x_971_);
v_i_962_ = v___x_972_;
v_b_964_ = v_a_970_;
goto _start;
}
else
{
return v___x_969_;
}
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_b_964_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* v_as_975_, lean_object* v_i_976_, lean_object* v_stop_977_, lean_object* v_b_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
size_t v_i_boxed_981_; size_t v_stop_boxed_982_; lean_object* v_res_983_; 
v_i_boxed_981_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_stop_boxed_982_ = lean_unbox_usize(v_stop_977_);
lean_dec(v_stop_977_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_975_, v_i_boxed_981_, v_stop_boxed_982_, v_b_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v_as_975_);
return v_res_983_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; lean_object* v___y_990_; lean_object* v___x_994_; 
v___x_988_ = 1;
v___x_994_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
switch(lean_obj_tag(v___x_994_))
{
case 0:
{
lean_object* v_code_995_; 
v_code_995_ = lean_ctor_get(v___x_994_, 2);
v___y_990_ = v_code_995_;
goto v___jp_989_;
}
case 1:
{
lean_object* v_code_996_; 
v_code_996_ = lean_ctor_get(v___x_994_, 1);
v___y_990_ = v_code_996_;
goto v___jp_989_;
}
default: 
{
lean_object* v_code_997_; 
v_code_997_ = lean_ctor_get(v___x_994_, 0);
v___y_990_ = v_code_997_;
goto v___jp_989_;
}
}
v___jp_989_:
{
if (lean_obj_tag(v___y_990_) == 6)
{
size_t v___x_991_; size_t v___x_992_; 
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_985_, v___x_991_);
v_i_985_ = v___x_992_;
goto _start;
}
else
{
return v___x_988_;
}
}
}
else
{
uint8_t v___x_998_; 
v___x_998_ = 0;
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v_as_999_, lean_object* v_i_1000_, lean_object* v_stop_1001_){
_start:
{
size_t v_i_boxed_1002_; size_t v_stop_boxed_1003_; uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_i_boxed_1002_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_stop_boxed_1003_ = lean_unbox_usize(v_stop_1001_);
lean_dec(v_stop_1001_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_999_, v_i_boxed_1002_, v_stop_boxed_1003_);
lean_dec_ref(v_as_999_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1006_, uint8_t v_t_1007_, lean_object* v_i_1008_, lean_object* v_as_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = lean_array_get_size(v_as_1009_);
v___x_1014_ = lean_nat_dec_lt(v_i_1008_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec(v_i_1008_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_as_1009_);
return v___x_1015_;
}
else
{
lean_object* v_a_1016_; lean_object* v_type_1017_; lean_object* v___x_1018_; lean_object* v_subst_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1016_ = lean_array_fget_borrowed(v_as_1009_, v_i_1008_);
v_type_1017_ = lean_ctor_get(v_a_1016_, 2);
v___x_1018_ = lean_st_ref_get(v___y_1010_);
v_subst_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_ref(v_subst_1019_);
lean_dec(v___x_1018_);
lean_inc_ref(v_type_1017_);
v___x_1020_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1006_, v_subst_1019_, v_t_1007_, v_type_1017_);
lean_dec_ref(v_subst_1019_);
lean_inc(v_a_1016_);
v___x_1021_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1006_, v_a_1016_, v___x_1020_, v___y_1011_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; size_t v___x_1023_; size_t v___x_1024_; uint8_t v___x_1025_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = lean_ptr_addr(v_a_1016_);
v___x_1024_ = lean_ptr_addr(v_a_1022_);
v___x_1025_ = lean_usize_dec_eq(v___x_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_i_1008_, v___x_1026_);
v___x_1028_ = lean_array_fset(v_as_1009_, v_i_1008_, v_a_1022_);
lean_dec(v_i_1008_);
v_i_1008_ = v___x_1027_;
v_as_1009_ = v___x_1028_;
goto _start;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v_a_1022_);
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v_i_1008_, v___x_1030_);
lean_dec(v_i_1008_);
v_i_1008_ = v___x_1031_;
goto _start;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_as_1009_);
lean_dec(v_i_1008_);
v_a_1033_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1021_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1021_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1041_, lean_object* v_t_1042_, lean_object* v_i_1043_, lean_object* v_as_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v_pu_boxed_1048_; uint8_t v_t_boxed_1049_; lean_object* v_res_1050_; 
v_pu_boxed_1048_ = lean_unbox(v_pu_1041_);
v_t_boxed_1049_ = lean_unbox(v_t_1042_);
v_res_1050_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1048_, v_t_boxed_1049_, v_i_1043_, v_as_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1051_, uint8_t v_t_1052_, lean_object* v_ps_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1051_, v_t_1052_, v___x_1062_, v_ps_1053_, v___y_1055_, v___y_1058_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1064_, lean_object* v_t_1065_, lean_object* v_ps_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v_pu_boxed_1075_; uint8_t v_t_boxed_1076_; lean_object* v_res_1077_; 
v_pu_boxed_1075_ = lean_unbox(v_pu_1064_);
v_t_boxed_1076_ = lean_unbox(v_t_1065_);
v_res_1077_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1075_, v_t_boxed_1076_, v_ps_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1078_, uint8_t v_t_1079_, lean_object* v_decl_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_type_1084_; lean_object* v_value_1085_; lean_object* v___x_1086_; lean_object* v_subst_1087_; lean_object* v___x_1088_; lean_object* v_subst_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_type_1084_ = lean_ctor_get(v_decl_1080_, 2);
v_value_1085_ = lean_ctor_get(v_decl_1080_, 3);
v___x_1086_ = lean_st_ref_get(v___y_1081_);
v_subst_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_subst_1087_);
lean_dec(v___x_1086_);
v___x_1088_ = lean_st_ref_get(v___y_1081_);
v_subst_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_subst_1089_);
lean_dec(v___x_1088_);
lean_inc_ref(v_type_1084_);
v___x_1090_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1078_, v_subst_1087_, v_t_1079_, v_type_1084_);
lean_dec_ref(v_subst_1087_);
lean_inc(v_value_1085_);
v___x_1091_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1078_, v_subst_1089_, v_value_1085_, v_t_1079_);
lean_dec_ref(v_subst_1089_);
v___x_1092_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1078_, v_decl_1080_, v___x_1090_, v___x_1091_, v___y_1082_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1093_, lean_object* v_t_1094_, lean_object* v_decl_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_pu_boxed_1099_; uint8_t v_t_boxed_1100_; lean_object* v_res_1101_; 
v_pu_boxed_1099_ = lean_unbox(v_pu_1093_);
v_t_boxed_1100_ = lean_unbox(v_t_1094_);
v_res_1101_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1099_, v_t_boxed_1100_, v_decl_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1102_, lean_object* v___f_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v_fvarId_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
lean_inc(v_fvarId_1106_);
v___x_1112_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1106_, v___y_1102_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref_known(v___x_1112_, 1);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1107_);
lean_inc_ref(v___y_1105_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1104_);
v___x_1113_ = lean_apply_9(v___f_1103_, v_fvarId_1106_, v___y_1104_, v___y_1102_, v___y_1105_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, lean_box(0));
return v___x_1113_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_fvarId_1106_);
lean_dec_ref(v___f_1103_);
v_a_1114_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1112_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1122_, lean_object* v___f_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v_fvarId_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1122_, v___f_1123_, v___y_1124_, v___y_1125_, v_fvarId_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1122_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1162_; 
v_ks_1137_ = lean_ctor_get(v_x_1133_, 0);
v_vs_1138_ = lean_ctor_get(v_x_1133_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1140_ = v_x_1133_;
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_vs_1138_);
lean_inc(v_ks_1137_);
lean_dec(v_x_1133_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_array_get_size(v_ks_1137_);
v___x_1143_ = lean_nat_dec_lt(v_x_1134_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_x_1134_);
v___x_1144_ = lean_array_push(v_ks_1137_, v_x_1135_);
v___x_1145_ = lean_array_push(v_vs_1138_, v_x_1136_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1145_);
lean_ctor_set(v___x_1140_, 0, v___x_1144_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v_k_x27_1149_; uint8_t v___x_1150_; 
v_k_x27_1149_ = lean_array_fget_borrowed(v_ks_1137_, v_x_1134_);
v___x_1150_ = lean_name_eq(v_x_1135_, v_k_x27_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
if (v_isShared_1141_ == 0)
{
v___x_1152_ = v___x_1140_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_ks_1137_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_vs_1138_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_x_1134_, v___x_1153_);
lean_dec(v_x_1134_);
v_x_1133_ = v___x_1152_;
v_x_1134_ = v___x_1154_;
goto _start;
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_array_fset(v_ks_1137_, v_x_1134_, v_x_1135_);
v___x_1158_ = lean_array_fset(v_vs_1138_, v_x_1134_, v_x_1136_);
lean_dec(v_x_1134_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1158_);
lean_ctor_set(v___x_1140_, 0, v___x_1157_);
v___x_1160_ = v___x_1140_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1163_, lean_object* v_k_1164_, lean_object* v_v_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1163_, v___x_1166_, v_k_1164_, v_v_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1169_, size_t v_x_1170_, size_t v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v_es_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v_j_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_es_1174_ = lean_ctor_get(v_x_1169_, 0);
v___x_1175_ = ((size_t)31ULL);
v___x_1176_ = lean_usize_land(v_x_1170_, v___x_1175_);
v_j_1177_ = lean_usize_to_nat(v___x_1176_);
v___x_1178_ = lean_array_get_size(v_es_1174_);
v___x_1179_ = lean_nat_dec_lt(v_j_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec(v_j_1177_);
lean_dec(v_x_1173_);
lean_dec(v_x_1172_);
return v_x_1169_;
}
else
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1218_; 
lean_inc_ref(v_es_1174_);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_x_1169_, 0);
lean_dec(v_unused_1219_);
v___x_1181_ = v_x_1169_;
v_isShared_1182_ = v_isSharedCheck_1218_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_x_1169_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1218_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_v_1183_; lean_object* v___x_1184_; lean_object* v_xs_x27_1185_; lean_object* v___y_1187_; 
v_v_1183_ = lean_array_fget(v_es_1174_, v_j_1177_);
v___x_1184_ = lean_box(0);
v_xs_x27_1185_ = lean_array_fset(v_es_1174_, v_j_1177_, v___x_1184_);
switch(lean_obj_tag(v_v_1183_))
{
case 0:
{
lean_object* v_key_1192_; lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1203_; 
v_key_1192_ = lean_ctor_get(v_v_1183_, 0);
v_val_1193_ = lean_ctor_get(v_v_1183_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_v_1183_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1195_ = v_v_1183_;
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_inc(v_key_1192_);
lean_dec(v_v_1183_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_name_eq(v_x_1172_, v_key_1192_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_del_object(v___x_1195_);
v___x_1198_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1192_, v_val_1193_, v_x_1172_, v_x_1173_);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___y_1187_ = v___x_1199_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1201_; 
lean_dec(v_val_1193_);
lean_dec(v_key_1192_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_x_1173_);
lean_ctor_set(v___x_1195_, 0, v_x_1172_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_x_1172_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_x_1173_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v___y_1187_ = v___x_1201_;
goto v___jp_1186_;
}
}
}
}
case 1:
{
lean_object* v_node_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1216_; 
v_node_1204_ = lean_ctor_get(v_v_1183_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_v_1183_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1206_ = v_v_1183_;
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_node_1204_);
lean_dec(v_v_1183_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1208_ = ((size_t)5ULL);
v___x_1209_ = lean_usize_shift_right(v_x_1170_, v___x_1208_);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_x_1171_, v___x_1210_);
v___x_1212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1204_, v___x_1209_, v___x_1211_, v_x_1172_, v_x_1173_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1212_);
v___x_1214_ = v___x_1206_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v___y_1187_ = v___x_1214_;
goto v___jp_1186_;
}
}
}
default: 
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_x_1172_);
lean_ctor_set(v___x_1217_, 1, v_x_1173_);
v___y_1187_ = v___x_1217_;
goto v___jp_1186_;
}
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_array_fset(v_xs_x27_1185_, v_j_1177_, v___y_1187_);
lean_dec(v_j_1177_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1188_);
v___x_1190_ = v___x_1181_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
else
{
lean_object* v_ks_1220_; lean_object* v_vs_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1239_; 
v_ks_1220_ = lean_ctor_get(v_x_1169_, 0);
v_vs_1221_ = lean_ctor_get(v_x_1169_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1223_ = v_x_1169_;
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_vs_1221_);
lean_inc(v_ks_1220_);
lean_dec(v_x_1169_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1239_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_ks_1220_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_vs_1221_);
v___x_1226_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v_newNode_1227_; size_t v___x_1228_; uint8_t v___x_1229_; 
v_newNode_1227_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1226_, v_x_1172_, v_x_1173_);
v___x_1228_ = ((size_t)7ULL);
v___x_1229_ = lean_usize_dec_le(v___x_1228_, v_x_1171_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1227_);
v___x_1231_ = lean_unsigned_to_nat(4u);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
lean_dec(v___x_1230_);
if (v___x_1232_ == 0)
{
lean_object* v_ks_1233_; lean_object* v_vs_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_ks_1233_ = lean_ctor_get(v_newNode_1227_, 0);
lean_inc_ref(v_ks_1233_);
v_vs_1234_ = lean_ctor_get(v_newNode_1227_, 1);
lean_inc_ref(v_vs_1234_);
lean_dec_ref(v_newNode_1227_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1171_, v_ks_1233_, v_vs_1234_, v___x_1235_, v___x_1236_);
lean_dec_ref(v_vs_1234_);
lean_dec_ref(v_ks_1233_);
return v___x_1237_;
}
else
{
return v_newNode_1227_;
}
}
else
{
return v_newNode_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1240_, lean_object* v_keys_1241_, lean_object* v_vals_1242_, lean_object* v_i_1243_, lean_object* v_entries_1244_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_keys_1241_);
v___x_1246_ = lean_nat_dec_lt(v_i_1243_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v_i_1243_);
return v_entries_1244_;
}
else
{
lean_object* v_k_1247_; lean_object* v_v_1248_; uint64_t v___y_1250_; 
v_k_1247_ = lean_array_fget_borrowed(v_keys_1241_, v_i_1243_);
v_v_1248_ = lean_array_fget_borrowed(v_vals_1242_, v_i_1243_);
if (lean_obj_tag(v_k_1247_) == 0)
{
uint64_t v___x_1261_; 
v___x_1261_ = 1723ULL;
v___y_1250_ = v___x_1261_;
goto v___jp_1249_;
}
else
{
uint64_t v_hash_1262_; 
v_hash_1262_ = lean_ctor_get_uint64(v_k_1247_, sizeof(void*)*2);
v___y_1250_ = v_hash_1262_;
goto v___jp_1249_;
}
v___jp_1249_:
{
size_t v_h_1251_; size_t v___x_1252_; lean_object* v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v_h_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_h_1251_ = lean_uint64_to_usize(v___y_1250_);
v___x_1252_ = ((size_t)5ULL);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_sub(v_depth_1240_, v___x_1254_);
v___x_1256_ = lean_usize_mul(v___x_1252_, v___x_1255_);
v_h_1257_ = lean_usize_shift_right(v_h_1251_, v___x_1256_);
v___x_1258_ = lean_nat_add(v_i_1243_, v___x_1253_);
lean_dec(v_i_1243_);
lean_inc(v_v_1248_);
lean_inc(v_k_1247_);
v___x_1259_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1244_, v_h_1257_, v_depth_1240_, v_k_1247_, v_v_1248_);
v_i_1243_ = v___x_1258_;
v_entries_1244_ = v___x_1259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1263_, lean_object* v_keys_1264_, lean_object* v_vals_1265_, lean_object* v_i_1266_, lean_object* v_entries_1267_){
_start:
{
size_t v_depth_boxed_1268_; lean_object* v_res_1269_; 
v_depth_boxed_1268_ = lean_unbox_usize(v_depth_1263_);
lean_dec(v_depth_1263_);
v_res_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1268_, v_keys_1264_, v_vals_1265_, v_i_1266_, v_entries_1267_);
lean_dec_ref(v_vals_1265_);
lean_dec_ref(v_keys_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_43364__boxed_1275_; size_t v_x_43365__boxed_1276_; lean_object* v_res_1277_; 
v_x_43364__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_x_43365__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1270_, v_x_43364__boxed_1275_, v_x_43365__boxed_1276_, v_x_1273_, v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint64_t v___y_1282_; 
if (lean_obj_tag(v_x_1279_) == 0)
{
uint64_t v___x_1286_; 
v___x_1286_ = 1723ULL;
v___y_1282_ = v___x_1286_;
goto v___jp_1281_;
}
else
{
uint64_t v_hash_1287_; 
v_hash_1287_ = lean_ctor_get_uint64(v_x_1279_, sizeof(void*)*2);
v___y_1282_ = v_hash_1287_;
goto v___jp_1281_;
}
v___jp_1281_:
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_uint64_to_usize(v___y_1282_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1278_, v___x_1283_, v___x_1284_, v_x_1279_, v_x_1280_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1288_, lean_object* v_b_1289_){
_start:
{
lean_object* v_array_1290_; lean_object* v_start_1291_; lean_object* v_stop_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1305_; 
v_array_1290_ = lean_ctor_get(v_a_1288_, 0);
v_start_1291_ = lean_ctor_get(v_a_1288_, 1);
v_stop_1292_ = lean_ctor_get(v_a_1288_, 2);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1294_ = v_a_1288_;
v_isShared_1295_ = v_isSharedCheck_1305_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_stop_1292_);
lean_inc(v_start_1291_);
lean_inc(v_array_1290_);
lean_dec(v_a_1288_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1305_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_nat_dec_lt(v_start_1291_, v_stop_1292_);
if (v___x_1296_ == 0)
{
lean_del_object(v___x_1294_);
lean_dec(v_stop_1292_);
lean_dec(v_start_1291_);
lean_dec_ref(v_array_1290_);
return v_b_1289_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_start_1291_, v___x_1297_);
lean_inc_ref(v_array_1290_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 1, v___x_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_array_1290_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_stop_1292_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_array_fget(v_array_1290_, v_start_1291_);
lean_dec(v_start_1291_);
lean_dec_ref(v_array_1290_);
v___x_1302_ = lean_array_push(v_b_1289_, v___x_1301_);
v_a_1288_ = v___x_1300_;
v_b_1289_ = v___x_1302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1306_, size_t v_sz_1307_, size_t v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1308_, v_sz_1307_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_b_1309_);
return v___x_1313_;
}
else
{
lean_object* v_array_1314_; lean_object* v_start_1315_; lean_object* v_stop_1316_; uint8_t v___x_1317_; 
v_array_1314_ = lean_ctor_get(v_b_1309_, 0);
v_start_1315_ = lean_ctor_get(v_b_1309_, 1);
v_stop_1316_ = lean_ctor_get(v_b_1309_, 2);
v___x_1317_ = lean_nat_dec_lt(v_start_1315_, v_stop_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_b_1309_);
return v___x_1318_;
}
else
{
lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_stop_1316_);
lean_inc(v_start_1315_);
lean_inc_ref(v_array_1314_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_b_1309_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1352_ = lean_ctor_get(v_b_1309_, 2);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_b_1309_, 1);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_b_1309_, 0);
lean_dec(v_unused_1354_);
v___x_1320_ = v_b_1309_;
v_isShared_1321_ = v_isSharedCheck_1351_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v_b_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1351_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v_a_1323_; lean_object* v_fvarId_1324_; lean_object* v_subst_1325_; lean_object* v_used_1326_; lean_object* v_binderRenaming_1327_; lean_object* v_funDeclInfoMap_1328_; uint8_t v_simplified_1329_; lean_object* v_visited_1330_; lean_object* v_inline_1331_; lean_object* v_inlineLocal_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1350_; 
v___x_1322_ = lean_st_ref_take(v___y_1310_);
v_a_1323_ = lean_array_uget_borrowed(v_as_1306_, v_i_1308_);
v_fvarId_1324_ = lean_ctor_get(v_a_1323_, 0);
v_subst_1325_ = lean_ctor_get(v___x_1322_, 0);
v_used_1326_ = lean_ctor_get(v___x_1322_, 1);
v_binderRenaming_1327_ = lean_ctor_get(v___x_1322_, 2);
v_funDeclInfoMap_1328_ = lean_ctor_get(v___x_1322_, 3);
v_simplified_1329_ = lean_ctor_get_uint8(v___x_1322_, sizeof(void*)*7);
v_visited_1330_ = lean_ctor_get(v___x_1322_, 4);
v_inline_1331_ = lean_ctor_get(v___x_1322_, 5);
v_inlineLocal_1332_ = lean_ctor_get(v___x_1322_, 6);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_inlineLocal_1332_);
lean_inc(v_inline_1331_);
lean_inc(v_visited_1330_);
lean_inc(v_funDeclInfoMap_1328_);
lean_inc(v_binderRenaming_1327_);
lean_inc(v_used_1326_);
lean_inc(v_subst_1325_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_array_fget_borrowed(v_array_1314_, v_start_1315_);
lean_inc(v___x_1336_);
lean_inc(v_fvarId_1324_);
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1325_, v_fvarId_1324_, v___x_1336_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_used_1326_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_binderRenaming_1327_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_funDeclInfoMap_1328_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_visited_1330_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_inline_1331_);
lean_ctor_set(v_reuseFailAlloc_1349_, 6, v_inlineLocal_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*7, v_simplified_1329_);
v___x_1339_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1340_ = lean_st_ref_put(v___y_1310_, v___x_1339_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_add(v_start_1315_, v___x_1341_);
lean_dec(v_start_1315_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1342_);
v___x_1344_ = v___x_1320_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_array_1314_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_stop_1316_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
size_t v___x_1345_; size_t v___x_1346_; 
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1308_, v___x_1345_);
v_i_1308_ = v___x_1346_;
v_b_1309_ = v___x_1344_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1355_, lean_object* v_sz_1356_, lean_object* v_i_1357_, lean_object* v_b_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
size_t v_sz_boxed_1361_; size_t v_i_boxed_1362_; lean_object* v_res_1363_; 
v_sz_boxed_1361_ = lean_unbox_usize(v_sz_1356_);
lean_dec(v_sz_1356_);
v_i_boxed_1362_ = lean_unbox_usize(v_i_1357_);
lean_dec(v_i_1357_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1355_, v_sz_boxed_1361_, v_i_boxed_1362_, v_b_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v_as_1355_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1364_, size_t v_i_1365_, size_t v_stop_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_eq(v_i_1365_, v_stop_1366_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = 0;
v___x_1372_ = lean_array_uget_borrowed(v_as_1364_, v_i_1365_);
v___x_1373_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1371_, v___x_1372_, v___y_1368_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; size_t v___x_1375_; size_t v___x_1376_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1365_, v___x_1375_);
v_i_1365_ = v___x_1376_;
v_b_1367_ = v_a_1374_;
goto _start;
}
else
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_b_1367_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_stop_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1381_);
lean_dec(v_stop_1381_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1379_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v_as_1379_);
return v_res_1387_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = 0;
v___x_1389_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1392_ = lean_panic_fn_borrowed(v___x_1391_, v_msg_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1393_, size_t v_i_1394_, size_t v_stop_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_usize_dec_eq(v_i_1394_, v_stop_1395_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v_type_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_array_uget_borrowed(v_as_1393_, v_i_1394_);
v_type_1400_ = lean_ctor_get(v___x_1399_, 2);
v___x_1401_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1400_, v___y_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1413_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_unbox(v_a_1402_);
if (v___x_1406_ == 0)
{
size_t v___x_1407_; size_t v___x_1408_; 
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_add(v_i_1394_, v___x_1407_);
v_i_1394_ = v___x_1408_;
goto _start;
}
else
{
lean_object* v___x_1411_; 
if (v_isShared_1405_ == 0)
{
v___x_1411_ = v___x_1404_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1402_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
return v___x_1401_;
}
}
else
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = 0;
v___x_1415_ = lean_box(v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1417_, lean_object* v_i_1418_, lean_object* v_stop_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
size_t v_i_boxed_1422_; size_t v_stop_boxed_1423_; lean_object* v_res_1424_; 
v_i_boxed_1422_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_stop_boxed_1423_ = lean_unbox_usize(v_stop_1419_);
lean_dec(v_stop_1419_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1417_, v_i_boxed_1422_, v_stop_boxed_1423_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v_as_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1425_, size_t v_i_1426_, size_t v_stop_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_eq(v_i_1426_, v_stop_1427_);
if (v___x_1431_ == 0)
{
uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = 0;
v___x_1433_ = lean_array_uget_borrowed(v_as_1425_, v_i_1426_);
v___x_1434_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1432_, v___x_1433_, v___y_1429_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; size_t v___x_1436_; size_t v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1426_, v___x_1436_);
v_i_1426_ = v___x_1437_;
v_b_1428_ = v_a_1435_;
goto _start;
}
else
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_b_1428_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1440_, lean_object* v_i_1441_, lean_object* v_stop_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
size_t v_i_boxed_1446_; size_t v_stop_boxed_1447_; lean_object* v_res_1448_; 
v_i_boxed_1446_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_stop_boxed_1447_ = lean_unbox_usize(v_stop_1442_);
lean_dec(v_stop_1442_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1440_, v_i_boxed_1446_, v_stop_boxed_1447_, v_b_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v_as_1440_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1449_, size_t v_i_1450_, size_t v_stop_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_a_1459_; lean_object* v___y_1464_; uint8_t v___x_1466_; 
v___x_1466_ = lean_usize_dec_eq(v_i_1450_, v_stop_1451_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_array_uget_borrowed(v_as_1449_, v_i_1450_);
v___x_1469_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1468_);
v___x_1470_ = lean_array_get_size(v___x_1469_);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_nat_dec_lt(v___x_1467_, v___x_1470_);
if (v___x_1472_ == 0)
{
lean_dec_ref(v___x_1469_);
v_a_1459_ = v___x_1471_;
goto v___jp_1458_;
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_nat_dec_le(v___x_1470_, v___x_1470_);
if (v___x_1473_ == 0)
{
if (v___x_1472_ == 0)
{
lean_dec_ref(v___x_1469_);
v_a_1459_ = v___x_1471_;
goto v___jp_1458_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = lean_usize_of_nat(v___x_1470_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1469_, v___x_1474_, v___x_1475_, v___x_1471_, v___y_1454_);
lean_dec_ref(v___x_1469_);
v___y_1464_ = v___x_1476_;
goto v___jp_1463_;
}
}
else
{
size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1470_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1469_, v___x_1477_, v___x_1478_, v___x_1471_, v___y_1454_);
lean_dec_ref(v___x_1469_);
v___y_1464_ = v___x_1479_;
goto v___jp_1463_;
}
}
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_b_1452_);
return v___x_1480_;
}
v___jp_1458_:
{
size_t v___x_1460_; size_t v___x_1461_; 
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_add(v_i_1450_, v___x_1460_);
v_i_1450_ = v___x_1461_;
v_b_1452_ = v_a_1459_;
goto _start;
}
v___jp_1463_:
{
if (lean_obj_tag(v___y_1464_) == 0)
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v___y_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___y_1464_, 1);
v_a_1459_ = v_a_1465_;
goto v___jp_1458_;
}
else
{
return v___y_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1481_, lean_object* v_i_1482_, lean_object* v_stop_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
size_t v_i_boxed_1490_; size_t v_stop_boxed_1491_; lean_object* v_res_1492_; 
v_i_boxed_1490_ = lean_unbox_usize(v_i_1482_);
lean_dec(v_i_1482_);
v_stop_boxed_1491_ = lean_unbox_usize(v_stop_1483_);
lean_dec(v_stop_1483_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1481_, v_i_boxed_1490_, v_stop_boxed_1491_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec_ref(v_as_1481_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1493_, size_t v_i_1494_, size_t v_stop_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_eq(v_i_1494_, v_stop_1495_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v_fvarId_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_array_uget_borrowed(v_as_1493_, v_i_1494_);
v_fvarId_1500_ = lean_ctor_get(v___x_1499_, 0);
v___x_1501_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1500_, v___y_1496_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1513_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1513_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1513_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_a_1502_);
if (v___x_1506_ == 0)
{
size_t v___x_1507_; size_t v___x_1508_; 
lean_del_object(v___x_1504_);
lean_dec(v_a_1502_);
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1494_, v___x_1507_);
v_i_1494_ = v___x_1508_;
goto _start;
}
else
{
lean_object* v___x_1511_; 
if (v_isShared_1505_ == 0)
{
v___x_1511_ = v___x_1504_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1502_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
return v___x_1501_;
}
}
else
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = 0;
v___x_1515_ = lean_box(v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1517_, lean_object* v_i_1518_, lean_object* v_stop_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
size_t v_i_boxed_1522_; size_t v_stop_boxed_1523_; lean_object* v_res_1524_; 
v_i_boxed_1522_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_stop_boxed_1523_ = lean_unbox_usize(v_stop_1519_);
lean_dec(v_stop_1519_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1517_, v_i_boxed_1522_, v_stop_boxed_1523_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v_as_1517_);
return v_res_1524_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1528_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1529_ = lean_unsigned_to_nat(9u);
v___x_1530_ = lean_unsigned_to_nat(650u);
v___x_1531_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1533_ = l_mkPanicMessageWithDecl(v___x_1532_, v___x_1531_, v___x_1530_, v___x_1529_, v___x_1528_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(uint8_t v___x_1537_, lean_object* v_fvarId_1538_, lean_object* v_k_1539_, lean_object* v_args_1540_, uint8_t v___x_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v_result_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_lower_1555_; lean_object* v_upper_1556_; 
if (v___x_1537_ == 0)
{
lean_object* v___x_1583_; 
lean_dec(v___x_1544_);
lean_dec(v___x_1543_);
lean_dec(v___x_1542_);
lean_dec_ref(v_args_1540_);
v___x_1583_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1538_, v_result_1545_, v___y_1547_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1583_, 1);
lean_inc_ref(v___y_1551_);
v___x_1584_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1539_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1584_;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_k_1539_);
v_a_1585_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1583_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_le(v___x_1542_, v___x_1543_);
if (v___x_1593_ == 0)
{
lean_dec(v___x_1543_);
v_lower_1555_ = v___x_1542_;
v_upper_1556_ = v___x_1544_;
goto v___jp_1554_;
}
else
{
lean_dec(v___x_1542_);
v_lower_1555_ = v___x_1543_;
v_upper_1556_ = v___x_1544_;
goto v___jp_1554_;
}
}
v___jp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1557_ = l_Array_toSubarray___redArg(v_args_1540_, v_lower_1555_, v_upper_1556_);
v___x_1558_ = l_Subarray_copy___redArg(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_result_1545_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1561_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1541_, v___x_1559_, v___x_1560_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_fvarId_1563_; lean_object* v___x_1564_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_fvarId_1563_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_fvarId_1563_);
v___x_1564_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1538_, v_fvarId_1563_, v___y_1547_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1562_);
lean_ctor_set(v___x_1565_, 1, v_k_1539_);
lean_inc_ref(v___y_1551_);
v___x_1566_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1565_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1566_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1562_);
lean_dec_ref(v_k_1539_);
v_a_1567_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1564_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1564_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_k_1539_);
lean_dec(v_fvarId_1538_);
v_a_1575_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1561_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1561_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object** _args){
lean_object* v___x_1594_ = _args[0];
lean_object* v_fvarId_1595_ = _args[1];
lean_object* v_k_1596_ = _args[2];
lean_object* v_args_1597_ = _args[3];
lean_object* v___x_1598_ = _args[4];
lean_object* v___x_1599_ = _args[5];
lean_object* v___x_1600_ = _args[6];
lean_object* v___x_1601_ = _args[7];
lean_object* v_result_1602_ = _args[8];
lean_object* v___y_1603_ = _args[9];
lean_object* v___y_1604_ = _args[10];
lean_object* v___y_1605_ = _args[11];
lean_object* v___y_1606_ = _args[12];
lean_object* v___y_1607_ = _args[13];
lean_object* v___y_1608_ = _args[14];
lean_object* v___y_1609_ = _args[15];
lean_object* v___y_1610_ = _args[16];
_start:
{
uint8_t v___x_43878__boxed_1611_; uint8_t v___x_43879__boxed_1612_; lean_object* v_res_1613_; 
v___x_43878__boxed_1611_ = lean_unbox(v___x_1594_);
v___x_43879__boxed_1612_ = lean_unbox(v___x_1598_);
v_res_1613_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_43878__boxed_1611_, v_fvarId_1595_, v_k_1596_, v_args_1597_, v___x_43879__boxed_1612_, v___x_1599_, v___x_1600_, v___x_1601_, v_result_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1614_, lean_object* v_k_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_fvarId_1624_; lean_object* v_value_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1965_; 
v_fvarId_1624_ = lean_ctor_get(v_letDecl_1614_, 0);
v_value_1625_ = lean_ctor_get(v_letDecl_1614_, 3);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_letDecl_1614_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; 
v_unused_1966_ = lean_ctor_get(v_letDecl_1614_, 2);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_letDecl_1614_, 1);
lean_dec(v_unused_1967_);
v___x_1627_ = v_letDecl_1614_;
v_isShared_1628_ = v_isSharedCheck_1965_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_value_1625_);
lean_inc(v_fvarId_1624_);
lean_dec(v_letDecl_1614_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1965_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; 
lean_inc(v_value_1625_);
v___x_1629_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1625_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1956_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1956_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1956_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
if (lean_obj_tag(v_a_1630_) == 1)
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1951_; 
lean_del_object(v___x_1632_);
v_val_1634_ = lean_ctor_get(v_a_1630_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1630_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1636_ = v_a_1630_;
v_isShared_1637_ = v_isSharedCheck_1951_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v_a_1630_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1951_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_params_1638_; lean_object* v_value_1639_; lean_object* v_fType_1640_; lean_object* v_args_1641_; uint8_t v_recursive_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; uint8_t v___y_1658_; lean_object* v___y_1659_; uint8_t v___x_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; 
v_params_1638_ = lean_ctor_get(v_val_1634_, 0);
v_value_1639_ = lean_ctor_get(v_val_1634_, 1);
v_fType_1640_ = lean_ctor_get(v_val_1634_, 2);
v_args_1641_ = lean_ctor_get(v_val_1634_, 3);
v_recursive_1642_ = lean_ctor_get_uint8(v_val_1634_, sizeof(void*)*4 + 2);
v___x_1643_ = lean_array_get_size(v_args_1641_);
v___x_1644_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1634_);
v___x_1645_ = lean_nat_dec_lt(v___x_1643_, v___x_1644_);
v___x_1827_ = lean_nat_dec_lt(v___x_1644_, v___x_1643_);
if (lean_obj_tag(v_value_1625_) == 3)
{
lean_object* v_declName_1931_; lean_object* v___x_1932_; 
v_declName_1931_ = lean_ctor_get(v_value_1625_, 0);
lean_inc_n(v_declName_1931_, 2);
lean_dec_ref_known(v_value_1625_, 3);
v___x_1932_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1642_, v_declName_1931_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_declName_1934_; lean_object* v_config_1935_; lean_object* v_inlineStack_1936_; lean_object* v_inlineStackOccs_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_declName_1934_ = lean_ctor_get(v_a_1616_, 0);
v_config_1935_ = lean_ctor_get(v_a_1616_, 1);
v_inlineStack_1936_ = lean_ctor_get(v_a_1616_, 2);
v_inlineStackOccs_1937_ = lean_ctor_get(v_a_1616_, 3);
lean_inc(v_inlineStack_1936_);
lean_inc(v_declName_1931_);
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_declName_1931_);
lean_ctor_set(v___x_1938_, 1, v_inlineStack_1936_);
lean_inc_ref(v_inlineStackOccs_1937_);
v___x_1939_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1937_, v_declName_1931_, v_a_1933_);
lean_inc_ref(v_config_1935_);
lean_inc(v_declName_1934_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 3, v___x_1939_);
lean_ctor_set(v___x_1627_, 2, v___x_1938_);
lean_ctor_set(v___x_1627_, 1, v_config_1935_);
lean_ctor_set(v___x_1627_, 0, v_declName_1934_);
v___x_1941_ = v___x_1627_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_declName_1934_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_config_1935_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
v___y_1829_ = v___x_1941_;
v___y_1830_ = v_a_1617_;
v___y_1831_ = v_a_1618_;
v___y_1832_ = v_a_1619_;
v___y_1833_ = v_a_1620_;
v___y_1834_ = v_a_1621_;
v___y_1835_ = v_a_1622_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_declName_1931_);
lean_dec(v___x_1644_);
lean_del_object(v___x_1636_);
lean_dec(v_val_1634_);
lean_del_object(v___x_1627_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
v_a_1943_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1932_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1932_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_del_object(v___x_1627_);
lean_dec(v_value_1625_);
lean_inc_ref(v_a_1616_);
v___y_1829_ = v_a_1616_;
v___y_1830_ = v_a_1617_;
v___y_1831_ = v_a_1618_;
v___y_1832_ = v_a_1619_;
v___y_1833_ = v_a_1620_;
v___y_1834_ = v_a_1621_;
v___y_1835_ = v_a_1622_;
goto v___jp_1828_;
}
v___jp_1646_:
{
lean_object* v___x_1660_; 
lean_inc_ref(v___y_1653_);
v___x_1660_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1654_, v___y_1650_, v___y_1647_, v___y_1649_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1647_);
if (lean_obj_tag(v___x_1662_) == 0)
{
uint8_t v___x_1663_; 
lean_dec_ref_known(v___x_1662_, 1);
v___x_1663_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1661_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v___y_1651_);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___y_1648_);
lean_dec(v___y_1648_);
lean_inc_ref(v___x_1664_);
v___x_1665_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1657_, v___x_1664_);
v___x_1666_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1658_, v_fType_1640_, v___x_1665_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_n(v_a_1667_, 2);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_Expr_headBeta(v_a_1667_);
v___x_1669_ = l_Lean_Expr_isForall(v___x_1668_);
lean_dec_ref(v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec_ref(v___x_1664_);
v___x_1670_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1658_, v_a_1667_, v___x_1645_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_fvarId_1672_; lean_object* v___x_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v_fvarId_1672_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1652_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1647_);
lean_inc(v_fvarId_1672_);
v___x_1673_ = lean_apply_9(v___y_1656_, v_fvarId_1672_, v___y_1650_, v___y_1647_, v___y_1649_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_, lean_box(0));
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_mk_empty_array_with_capacity(v___x_1675_);
v___x_1677_ = lean_array_push(v___x_1676_, v_a_1671_);
v___x_1678_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1679_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1658_, v___x_1677_, v_a_1674_, v___x_1678_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_n(v_a_1680_, 2);
lean_dec_ref_known(v___x_1679_, 1);
v___f_1681_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1681_, 0, v_a_1680_);
lean_closure_set(v___f_1681_, 1, v___x_1675_);
v___x_1682_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1658_, v_a_1661_, v___f_1681_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1694_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1680_);
lean_ctor_set(v___x_1687_, 1, v_a_1683_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1687_);
v___x_1689_ = v___x_1636_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1680_);
lean_del_object(v___x_1636_);
v_a_1695_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1682_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1682_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1661_);
lean_del_object(v___x_1636_);
v_a_1703_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1679_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1679_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1671_);
lean_dec(v_a_1661_);
lean_del_object(v___x_1636_);
v_a_1711_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1673_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1673_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1661_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1650_);
lean_del_object(v___x_1636_);
v_a_1719_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1670_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1670_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_dec(v_a_1667_);
v___x_1727_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1728_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1664_, v_a_1661_, v___x_1727_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1729_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v_fvarId_1732_; lean_object* v___x_1733_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v_fvarId_1732_ = lean_ctor_get(v_a_1731_, 0);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1652_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1650_);
lean_inc(v_fvarId_1732_);
v___x_1733_ = lean_apply_9(v___y_1656_, v_fvarId_1732_, v___y_1650_, v___y_1647_, v___y_1649_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_, lean_box(0));
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_a_1731_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_mk_empty_array_with_capacity(v___x_1736_);
v___x_1738_ = lean_array_push(v___x_1737_, v___x_1735_);
v___x_1739_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1738_, v_a_1734_, v___y_1650_, v___y_1647_, v___y_1649_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
lean_dec_ref(v___y_1650_);
lean_dec_ref(v___x_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1750_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1750_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1750_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_a_1740_);
v___x_1745_ = v___x_1636_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_del_object(v___x_1636_);
v_a_1751_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1739_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1739_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1731_);
lean_dec_ref(v___y_1650_);
lean_del_object(v___x_1636_);
v_a_1759_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1733_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1733_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1650_);
lean_del_object(v___x_1636_);
v_a_1767_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1730_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1730_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1650_);
lean_del_object(v___x_1636_);
v_a_1775_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1728_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1728_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v___x_1664_);
lean_dec(v_a_1661_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1650_);
lean_del_object(v___x_1636_);
v_a_1783_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1666_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1666_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v___x_1791_; 
lean_dec_ref(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1648_);
lean_dec_ref(v_fType_1640_);
v___x_1791_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1658_, v_a_1661_, v___y_1651_, v___y_1652_, v___y_1655_, v___y_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1802_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_a_1792_);
v___x_1797_ = v___x_1636_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_del_object(v___x_1636_);
v_a_1803_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1791_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1791_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1661_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1648_);
lean_dec_ref(v_fType_1640_);
lean_del_object(v___x_1636_);
v_a_1811_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1662_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1662_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1648_);
lean_dec_ref(v_fType_1640_);
lean_del_object(v___x_1636_);
v_a_1819_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1660_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1660_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
v___jp_1828_:
{
if (v___x_1645_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_inc_ref_n(v_args_1641_, 2);
lean_inc_ref(v_fType_1640_);
lean_inc_ref(v_value_1639_);
lean_inc_ref(v_params_1638_);
lean_dec(v_val_1634_);
v___x_1836_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1644_);
v___x_1837_ = l_Array_toSubarray___redArg(v_args_1641_, v___x_1836_, v___x_1644_);
lean_inc_ref(v___x_1837_);
v___x_1838_ = l_Subarray_copy___redArg(v___x_1837_);
v___x_1839_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1638_, v_value_1639_, v___x_1838_, v___x_1645_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v_params_1638_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; uint8_t v___x_1846_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = 0;
v___x_1842_ = lean_box(v___x_1827_);
v___x_1843_ = lean_box(v___x_1841_);
lean_inc(v___x_1644_);
lean_inc_ref(v_k_1615_);
lean_inc(v_fvarId_1624_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1844_, 0, v___x_1842_);
lean_closure_set(v___f_1844_, 1, v_fvarId_1624_);
lean_closure_set(v___f_1844_, 2, v_k_1615_);
lean_closure_set(v___f_1844_, 3, v_args_1641_);
lean_closure_set(v___f_1844_, 4, v___x_1843_);
lean_closure_set(v___f_1844_, 5, v___x_1644_);
lean_closure_set(v___f_1844_, 6, v___x_1836_);
lean_closure_set(v___f_1844_, 7, v___x_1643_);
lean_inc_ref(v___y_1831_);
lean_inc_ref(v___y_1829_);
lean_inc_ref(v___f_1844_);
lean_inc(v___y_1830_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1845_, 0, v___y_1830_);
lean_closure_set(v___f_1845_, 1, v___f_1844_);
lean_closure_set(v___f_1845_, 2, v___y_1829_);
lean_closure_set(v___f_1845_, 3, v___y_1831_);
v___x_1846_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1615_, v_fvarId_1624_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
if (v___x_1846_ == 0)
{
lean_dec(v___x_1644_);
v___y_1647_ = v___y_1830_;
v___y_1648_ = v___x_1836_;
v___y_1649_ = v___y_1831_;
v___y_1650_ = v___y_1829_;
v___y_1651_ = v___f_1845_;
v___y_1652_ = v___y_1832_;
v___y_1653_ = v___y_1834_;
v___y_1654_ = v_a_1840_;
v___y_1655_ = v___y_1833_;
v___y_1656_ = v___f_1844_;
v___y_1657_ = v___x_1837_;
v___y_1658_ = v___x_1841_;
v___y_1659_ = v___y_1835_;
goto v___jp_1646_;
}
else
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_nat_dec_eq(v___x_1643_, v___x_1644_);
lean_dec(v___x_1644_);
if (v___x_1847_ == 0)
{
v___y_1647_ = v___y_1830_;
v___y_1648_ = v___x_1836_;
v___y_1649_ = v___y_1831_;
v___y_1650_ = v___y_1829_;
v___y_1651_ = v___f_1845_;
v___y_1652_ = v___y_1832_;
v___y_1653_ = v___y_1834_;
v___y_1654_ = v_a_1840_;
v___y_1655_ = v___y_1833_;
v___y_1656_ = v___f_1844_;
v___y_1657_ = v___x_1837_;
v___y_1658_ = v___x_1841_;
v___y_1659_ = v___y_1835_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1848_; 
lean_dec_ref(v___f_1845_);
lean_dec_ref(v___f_1844_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_fType_1640_);
lean_del_object(v___x_1636_);
v___x_1848_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1830_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v___x_1848_, 1);
lean_inc_ref(v___y_1834_);
v___x_1849_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1840_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v___y_1829_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1849_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1849_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1840_);
lean_dec_ref(v___y_1829_);
v_a_1867_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1848_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1848_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___y_1829_);
lean_dec(v___x_1644_);
lean_dec_ref(v_args_1641_);
lean_dec_ref(v_fType_1640_);
lean_del_object(v___x_1636_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
v_a_1875_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1839_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1839_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v___x_1883_; 
lean_dec(v___x_1644_);
lean_del_object(v___x_1636_);
v___x_1883_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1634_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_fvarId_1885_; lean_object* v___x_1886_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fvarId_1885_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_fvarId_1885_);
v___x_1886_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1624_, v_fvarId_1885_, v___y_1830_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref_known(v___x_1886_, 1);
v___x_1887_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1830_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref_known(v___x_1887_, 1);
v___x_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_a_1884_);
lean_ctor_set(v___x_1888_, 1, v_k_1615_);
lean_inc_ref(v___y_1834_);
v___x_1889_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1888_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v___y_1829_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1898_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1890_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1889_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1889_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1884_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_k_1615_);
v_a_1907_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1887_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1887_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1884_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_k_1615_);
v_a_1915_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1886_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1886_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v___y_1829_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
v_a_1923_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1883_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1883_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
lean_dec(v_a_1630_);
lean_del_object(v___x_1627_);
lean_dec(v_value_1625_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
v___x_1952_ = lean_box(0);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1952_);
v___x_1954_ = v___x_1632_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_del_object(v___x_1627_);
lean_dec(v_value_1625_);
lean_dec(v_fvarId_1624_);
lean_dec_ref(v_k_1615_);
v_a_1957_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1629_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1629_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = 0;
v___x_1969_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_typeName_1982_; lean_object* v_discr_1983_; lean_object* v___x_1984_; lean_object* v_subst_1985_; uint8_t v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; 
v_typeName_1982_ = lean_ctor_get(v_cases_1970_, 0);
v_discr_1983_ = lean_ctor_get(v_cases_1970_, 2);
v___x_1984_ = lean_st_ref_get(v_a_1972_);
v_subst_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc_ref(v_subst_1985_);
lean_dec(v___x_1984_);
v___x_1986_ = 0;
v___x_1987_ = 0;
lean_inc(v_discr_1983_);
v___x_1988_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1985_, v_discr_1983_, v___x_1987_);
lean_dec_ref(v_subst_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_fvarId_1989_; lean_object* v___x_1990_; 
v_fvarId_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_fvarId_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1989_, v_a_1973_, v_a_1975_, v_a_1977_);
lean_dec(v_fvarId_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2220_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2220_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2220_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
if (lean_obj_tag(v_a_1991_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2215_; 
v_val_1995_ = lean_ctor_get(v_a_1991_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_1997_ = v_a_1991_;
v_isShared_1998_ = v_isSharedCheck_2215_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v_a_1991_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2215_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v_env_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = lean_st_ref_get(v_a_1977_);
v_env_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_env_2000_);
lean_dec(v___x_1999_);
v___x_2001_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1995_);
lean_inc(v___x_2001_);
v___x_2002_ = l_Lean_Environment_find_x3f(v_env_2000_, v___x_2001_, v___x_1987_);
if (lean_obj_tag(v___x_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2214_; 
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2214_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2214_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
if (lean_obj_tag(v_val_2003_) == 6)
{
lean_object* v_val_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2213_; 
v_val_2007_ = lean_ctor_get(v_val_2003_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_val_2003_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2009_ = v_val_2003_;
v_isShared_2010_ = v_isSharedCheck_2213_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_val_2007_);
lean_dec(v_val_2003_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2213_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_induct_2011_; uint8_t v___x_2012_; 
v_induct_2011_ = lean_ctor_get(v_val_2007_, 1);
lean_inc(v_induct_2011_);
lean_dec_ref(v_val_2007_);
v___x_2012_ = lean_name_eq(v_typeName_1982_, v_induct_2011_);
lean_dec(v_induct_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_del_object(v___x_2009_);
lean_del_object(v___x_2005_);
lean_dec(v___x_2001_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
lean_dec_ref(v_cases_1970_);
v___x_2013_ = lean_box(0);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2013_);
v___x_2015_ = v___x_1993_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2212_; 
lean_del_object(v___x_1993_);
v___x_2017_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2018_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1986_, v_cases_1970_, v___x_2001_);
v_fst_2019_ = lean_ctor_get(v___x_2018_, 0);
v_snd_2020_ = lean_ctor_get(v___x_2018_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2212_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_snd_2020_);
lean_inc(v_fst_2019_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2212_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 4);
lean_ctor_set(v___x_2009_, 0, v_snd_2020_);
v___x_2025_ = v___x_2009_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_snd_2020_);
v___x_2025_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1986_, v___x_2025_, v_a_1975_);
lean_dec_ref(v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2026_, 1);
v___x_2027_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1972_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref_known(v___x_2027_, 1);
if (lean_obj_tag(v_fst_2019_) == 0)
{
if (lean_obj_tag(v_val_1995_) == 0)
{
lean_object* v_params_2028_; lean_object* v_code_2029_; lean_object* v_val_2030_; lean_object* v_args_2031_; lean_object* v_lower_2033_; lean_object* v_upper_2034_; lean_object* v_numParams_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
lean_del_object(v___x_2022_);
lean_del_object(v___x_1997_);
v_params_2028_ = lean_ctor_get(v_fst_2019_, 1);
lean_inc_ref(v_params_2028_);
v_code_2029_ = lean_ctor_get(v_fst_2019_, 2);
lean_inc_ref(v_code_2029_);
lean_dec_ref_known(v_fst_2019_, 3);
v_val_2030_ = lean_ctor_get(v_val_1995_, 0);
lean_inc_ref(v_val_2030_);
v_args_2031_ = lean_ctor_get(v_val_1995_, 1);
lean_inc_ref(v_args_2031_);
lean_dec_ref_known(v_val_1995_, 2);
v_numParams_2077_ = lean_ctor_get(v_val_2030_, 3);
lean_inc(v_numParams_2077_);
lean_dec_ref(v_val_2030_);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_array_get_size(v_args_2031_);
v___x_2080_ = lean_nat_dec_le(v_numParams_2077_, v___x_2078_);
if (v___x_2080_ == 0)
{
v_lower_2033_ = v_numParams_2077_;
v_upper_2034_ = v___x_2079_;
goto v___jp_2032_;
}
else
{
lean_dec(v_numParams_2077_);
v_lower_2033_ = v___x_2078_;
v_upper_2034_ = v___x_2079_;
goto v___jp_2032_;
}
v___jp_2032_:
{
lean_object* v___x_2035_; size_t v_sz_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2035_ = l_Array_toSubarray___redArg(v_args_2031_, v_lower_2033_, v_upper_2034_);
v_sz_2036_ = lean_array_size(v_params_2028_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2028_, v_sz_2036_, v___x_2037_, v___x_2035_, v_a_1972_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2039_; 
lean_dec_ref_known(v___x_2038_, 1);
lean_inc_ref(v_a_1976_);
v___x_2039_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2029_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1986_, v_params_2028_, v_a_1975_);
lean_dec_ref(v_params_2028_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2041_, 0);
lean_dec(v_unused_2052_);
v___x_2043_ = v___x_2041_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v___x_2041_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_a_2040_);
v___x_2046_ = v___x_2005_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2040_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2048_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2040_);
lean_del_object(v___x_2005_);
v_a_2053_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2041_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2041_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_params_2028_);
lean_del_object(v___x_2005_);
v_a_2061_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2039_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2039_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_code_2029_);
lean_dec_ref(v_params_2028_);
lean_del_object(v___x_2005_);
v_a_2069_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2038_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2038_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_object* v_params_2081_; lean_object* v_code_2082_; lean_object* v_n_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2173_; 
v_params_2081_ = lean_ctor_get(v_fst_2019_, 1);
lean_inc_ref(v_params_2081_);
v_code_2082_ = lean_ctor_get(v_fst_2019_, 2);
lean_inc_ref(v_code_2082_);
lean_dec_ref_known(v_fst_2019_, 3);
v_n_2083_ = lean_ctor_get(v_val_1995_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_val_1995_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2085_ = v_val_1995_;
v_isShared_2086_ = v_isSharedCheck_2173_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_n_2083_);
lean_dec(v_val_1995_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2173_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_zero_2087_; uint8_t v_isZero_2088_; 
v_zero_2087_ = lean_unsigned_to_nat(0u);
v_isZero_2088_ = lean_nat_dec_eq(v_n_2083_, v_zero_2087_);
if (v_isZero_2088_ == 1)
{
lean_object* v___x_2089_; 
lean_del_object(v___x_2085_);
lean_dec(v_n_2083_);
lean_dec_ref(v_params_2081_);
lean_del_object(v___x_2022_);
lean_del_object(v___x_1997_);
lean_inc_ref(v_a_1976_);
v___x_2089_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2082_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2100_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_a_2090_);
v___x_2095_ = v___x_2005_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2095_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_del_object(v___x_2005_);
v_a_2101_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2089_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2089_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_one_2109_; lean_object* v_n_2110_; lean_object* v___x_2112_; 
v_one_2109_ = lean_unsigned_to_nat(1u);
v_n_2110_ = lean_nat_sub(v_n_2083_, v_one_2109_);
lean_dec(v_n_2083_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 0);
lean_ctor_set(v___x_2085_, 0, v_n_2110_);
v___x_2112_ = v___x_2085_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_n_2110_);
v___x_2112_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 0);
lean_ctor_set(v___x_1997_, 0, v___x_2112_);
v___x_2114_ = v___x_1997_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2116_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1986_, v___x_2114_, v___x_2115_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; lean_object* v_fvarId_2119_; lean_object* v_fvarId_2120_; lean_object* v___x_2121_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = lean_array_get_borrowed(v___x_2017_, v_params_2081_, v_zero_2087_);
v_fvarId_2119_ = lean_ctor_get(v___x_2118_, 0);
v_fvarId_2120_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_fvarId_2120_);
lean_inc(v_fvarId_2119_);
v___x_2121_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2119_, v_fvarId_2120_, v_a_1972_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref_known(v___x_2121_, 1);
lean_inc_ref(v_a_1976_);
v___x_2122_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2082_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1986_, v_params_2081_, v_a_1975_);
lean_dec_ref(v_params_2081_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2124_, 0);
lean_dec(v_unused_2138_);
v___x_2126_ = v___x_2124_;
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v___x_2124_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v_a_2123_);
lean_ctor_set(v___x_2022_, 0, v_a_2117_);
v___x_2129_ = v___x_2022_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_a_2123_);
v___x_2129_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2129_);
v___x_2131_ = v___x_2005_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2131_);
v___x_2133_ = v___x_2126_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_a_2123_);
lean_dec(v_a_2117_);
lean_del_object(v___x_2022_);
lean_del_object(v___x_2005_);
v_a_2139_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2124_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2124_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_a_2117_);
lean_dec_ref(v_params_2081_);
lean_del_object(v___x_2022_);
lean_del_object(v___x_2005_);
v_a_2147_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2122_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2122_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2117_);
lean_dec_ref(v_code_2082_);
lean_dec_ref(v_params_2081_);
lean_del_object(v___x_2022_);
lean_del_object(v___x_2005_);
v_a_2155_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2121_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2121_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v_code_2082_);
lean_dec_ref(v_params_2081_);
lean_del_object(v___x_2022_);
lean_del_object(v___x_2005_);
v_a_2163_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2116_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2116_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
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
lean_object* v_code_2174_; lean_object* v___x_2175_; 
lean_del_object(v___x_2022_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
v_code_2174_ = lean_ctor_get(v_fst_2019_, 0);
lean_inc_ref(v_code_2174_);
lean_dec_ref_known(v_fst_2019_, 1);
lean_inc_ref(v_a_1976_);
v___x_2175_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2174_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2186_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_a_2176_);
v___x_2181_ = v___x_2005_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2183_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2181_);
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_del_object(v___x_2005_);
v_a_2187_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2175_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2175_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_del_object(v___x_2022_);
lean_dec(v_fst_2019_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
v_a_2195_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2027_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2027_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_del_object(v___x_2022_);
lean_dec(v_fst_2019_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
v_a_2203_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2026_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2026_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
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
lean_del_object(v___x_2005_);
lean_dec(v_val_2003_);
lean_dec(v___x_2001_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_cases_1970_);
goto v___jp_1979_;
}
}
}
else
{
lean_dec(v___x_2002_);
lean_dec(v___x_2001_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1995_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_cases_1970_);
goto v___jp_1979_;
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec(v_a_1991_);
lean_dec_ref(v_cases_1970_);
v___x_2216_ = lean_box(0);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2216_);
v___x_2218_ = v___x_1993_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_cases_1970_);
v_a_2221_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_1990_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_1990_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v___x_2229_; 
lean_dec_ref(v_cases_1970_);
v___x_2229_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1986_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2229_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
v___jp_1979_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2247_, lean_object* v_i_2248_, lean_object* v_as_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = lean_array_get_size(v_as_2249_);
v___x_2259_ = lean_nat_dec_lt(v_i_2248_, v___x_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_as_2249_);
return v___x_2260_;
}
else
{
lean_object* v_a_2261_; lean_object* v_a_2263_; 
v_a_2261_ = lean_array_fget_borrowed(v_as_2249_, v_i_2248_);
if (lean_obj_tag(v_a_2261_) == 0)
{
lean_object* v_ctorName_2274_; lean_object* v_params_2275_; lean_object* v_code_2276_; uint8_t v___x_2299_; uint8_t v_a_2301_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_ctorName_2274_ = lean_ctor_get(v_a_2261_, 0);
v_params_2275_ = lean_ctor_get(v_a_2261_, 1);
v_code_2276_ = lean_ctor_get(v_a_2261_, 2);
v___x_2299_ = 0;
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_array_get_size(v_params_2275_);
v___x_2334_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
v_a_2301_ = v___x_2334_;
goto v___jp_2300_;
}
else
{
if (v___x_2334_ == 0)
{
v_a_2301_ = v___x_2334_;
goto v___jp_2300_;
}
else
{
size_t v___x_2335_; size_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = lean_usize_of_nat(v___x_2333_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2275_, v___x_2335_, v___x_2336_, v___y_2256_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; uint8_t v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = lean_unbox(v_a_2338_);
lean_dec(v_a_2338_);
v_a_2301_ = v___x_2339_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2340_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2337_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2337_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
v___jp_2277_:
{
lean_object* v___x_2278_; 
lean_inc_ref(v_params_2275_);
lean_inc(v_ctorName_2274_);
lean_inc(v_fvarId_2247_);
v___x_2278_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2247_, v_ctorName_2274_, v_params_2275_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v_code_2276_);
v___x_2280_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2276_, v___y_2250_, v___y_2251_, v_a_2279_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v_a_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
lean_inc_ref(v_a_2261_);
v___x_2282_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2261_, v_a_2281_);
v_a_2263_ = v___x_2282_;
goto v___jp_2262_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2283_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2291_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2278_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2278_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
v___jp_2300_:
{
if (lean_obj_tag(v_code_2276_) == 6)
{
goto v___jp_2277_;
}
else
{
if (v_a_2301_ == 0)
{
goto v___jp_2277_;
}
else
{
lean_object* v___x_2302_; 
lean_inc_ref(v_code_2276_);
v___x_2302_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2299_, v_code_2276_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2299_, v_code_2276_, v___y_2254_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; 
lean_dec_ref_known(v___x_2304_, 1);
v___x_2305_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2251_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2306_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_a_2303_);
lean_inc_ref(v_a_2261_);
v___x_2307_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2261_, v___x_2306_);
v_a_2263_ = v___x_2307_;
goto v___jp_2262_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2308_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2305_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2305_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2316_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2304_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2304_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2324_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2302_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2302_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2348_; lean_object* v___x_2349_; 
v_code_2348_ = lean_ctor_get(v_a_2261_, 0);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v_code_2348_);
v___x_2349_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2348_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
lean_inc_ref(v_a_2261_);
v___x_2351_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2261_, v_a_2350_);
v_a_2263_ = v___x_2351_;
goto v___jp_2262_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_as_2249_);
lean_dec(v_i_2248_);
lean_dec(v_fvarId_2247_);
v_a_2352_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2349_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2349_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
v___jp_2262_:
{
size_t v___x_2264_; size_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2264_ = lean_ptr_addr(v_a_2261_);
v___x_2265_ = lean_ptr_addr(v_a_2263_);
v___x_2266_ = lean_usize_dec_eq(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_add(v_i_2248_, v___x_2267_);
v___x_2269_ = lean_array_fset(v_as_2249_, v_i_2248_, v_a_2263_);
lean_dec(v_i_2248_);
v_i_2248_ = v___x_2268_;
v_as_2249_ = v___x_2269_;
goto _start;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v_a_2263_);
v___x_2271_ = lean_unsigned_to_nat(1u);
v___x_2272_ = lean_nat_add(v_i_2248_, v___x_2271_);
lean_dec(v_i_2248_);
v_i_2248_ = v___x_2272_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2435_; lean_object* v___y_2436_; lean_object* v_decl_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2486_; lean_object* v___y_2487_; lean_object* v_decl_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_decl_2507_; lean_object* v_k_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_decl_2788_; lean_object* v_fvarId_2789_; lean_object* v_type_2790_; lean_object* v_value_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2880_; lean_object* v___y_2881_; uint8_t v___y_2882_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v_toCold_3284_; lean_object* v_currRecDepth_3285_; lean_object* v_ref_3286_; uint8_t v_diag_3287_; uint8_t v_suppressElabErrors_3288_; lean_object* v_maxRecDepth_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_toCold_3284_ = lean_ctor_get(v_a_2367_, 0);
v_currRecDepth_3285_ = lean_ctor_get(v_a_2367_, 1);
v_ref_3286_ = lean_ctor_get(v_a_2367_, 2);
v_diag_3287_ = lean_ctor_get_uint8(v_a_2367_, sizeof(void*)*3);
v_suppressElabErrors_3288_ = lean_ctor_get_uint8(v_a_2367_, sizeof(void*)*3 + 1);
v_maxRecDepth_3318_ = lean_ctor_get(v_toCold_3284_, 3);
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_nat_dec_eq(v_maxRecDepth_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_eq(v_currRecDepth_3285_, v_maxRecDepth_3318_);
if (v___x_3321_ == 0)
{
lean_inc(v_ref_3286_);
lean_inc(v_currRecDepth_3285_);
lean_inc_ref(v_toCold_3284_);
lean_dec_ref(v_a_2367_);
goto v___jp_3289_;
}
else
{
lean_object* v___x_3322_; 
lean_dec_ref(v_code_2361_);
v___x_3322_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
lean_dec_ref(v_a_2367_);
return v___x_3322_;
}
}
else
{
lean_inc(v_ref_3286_);
lean_inc(v_currRecDepth_3285_);
lean_inc_ref(v_toCold_3284_);
lean_dec_ref(v_a_2367_);
goto v___jp_3289_;
}
v___jp_2370_:
{
switch(lean_obj_tag(v_code_2361_))
{
case 1:
{
lean_object* v_decl_2373_; lean_object* v_k_2374_; size_t v___x_2375_; size_t v___x_2376_; uint8_t v___x_2377_; 
v_decl_2373_ = lean_ctor_get(v_code_2361_, 0);
v_k_2374_ = lean_ctor_get(v_code_2361_, 1);
v___x_2375_ = lean_ptr_addr(v_k_2374_);
v___x_2376_ = lean_ptr_addr(v___y_2371_);
v___x_2377_ = lean_usize_dec_eq(v___x_2375_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; 
v_unused_2386_ = lean_ctor_get(v_code_2361_, 1);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_2387_);
v___x_2379_ = v_code_2361_;
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v_code_2361_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___y_2371_);
lean_ctor_set(v___x_2379_, 0, v___y_2372_);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___y_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___y_2371_);
v___x_2382_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
}
else
{
size_t v___x_2388_; size_t v___x_2389_; uint8_t v___x_2390_; 
v___x_2388_ = lean_ptr_addr(v_decl_2373_);
v___x_2389_ = lean_ptr_addr(v___y_2372_);
v___x_2390_ = lean_usize_dec_eq(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_isSharedCheck_2398_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2399_ = lean_ctor_get(v_code_2361_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_2400_);
v___x_2392_ = v_code_2361_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_dec(v_code_2361_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v___y_2371_);
lean_ctor_set(v___x_2392_, 0, v___y_2372_);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___y_2372_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___y_2371_);
v___x_2395_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
else
{
lean_object* v___x_2401_; 
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2371_);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_code_2361_);
return v___x_2401_;
}
}
}
case 2:
{
lean_object* v_decl_2402_; lean_object* v_k_2403_; size_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v_decl_2402_ = lean_ctor_get(v_code_2361_, 0);
v_k_2403_ = lean_ctor_get(v_code_2361_, 1);
v___x_2404_ = lean_ptr_addr(v_k_2403_);
v___x_2405_ = lean_ptr_addr(v___y_2371_);
v___x_2406_ = lean_usize_dec_eq(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2414_; 
v_isSharedCheck_2414_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; 
v_unused_2415_ = lean_ctor_get(v_code_2361_, 1);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_2416_);
v___x_2408_ = v_code_2361_;
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v_code_2361_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___y_2371_);
lean_ctor_set(v___x_2408_, 0, v___y_2372_);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___y_2372_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___y_2371_);
v___x_2411_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
}
else
{
size_t v___x_2417_; size_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2417_ = lean_ptr_addr(v_decl_2402_);
v___x_2418_ = lean_ptr_addr(v___y_2372_);
v___x_2419_ = lean_usize_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
v_isSharedCheck_2427_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; lean_object* v_unused_2429_; 
v_unused_2428_ = lean_ctor_get(v_code_2361_, 1);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_2429_);
v___x_2421_ = v_code_2361_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v_code_2361_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___y_2371_);
lean_ctor_set(v___x_2421_, 0, v___y_2372_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___y_2372_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___y_2371_);
v___x_2424_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
}
else
{
lean_object* v___x_2430_; 
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2371_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_code_2361_);
return v___x_2430_;
}
}
}
default: 
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_code_2361_);
v___x_2431_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2432_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
}
v___jp_2434_:
{
lean_object* v___x_2445_; 
lean_inc_ref(v___y_2443_);
v___x_2445_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2436_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v_fvarId_2447_; lean_object* v___x_2448_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v_fvarId_2447_ = lean_ctor_get(v_decl_2437_, 0);
v___x_2448_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2447_, v___y_2439_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; uint8_t v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_unbox(v_a_2449_);
lean_dec(v_a_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_code_2361_);
v___x_2451_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2437_, v___y_2439_, v___y_2442_);
lean_dec_ref(v_decl_2437_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2451_, 0);
lean_dec(v_unused_2459_);
v___x_2453_ = v___x_2451_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v___x_2451_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_a_2446_);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2446_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_a_2446_);
v_a_2460_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2451_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2451_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
if (v___y_2435_ == 0)
{
lean_dec_ref(v___y_2443_);
v___y_2371_ = v_a_2446_;
v___y_2372_ = v_decl_2437_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2468_; 
lean_inc_ref(v_decl_2437_);
v___x_2468_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec_ref(v___y_2443_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_dec_ref_known(v___x_2468_, 1);
v___y_2371_ = v_a_2446_;
v___y_2372_ = v_decl_2437_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2446_);
lean_dec_ref(v_decl_2437_);
lean_dec_ref(v_code_2361_);
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2446_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_decl_2437_);
lean_dec_ref(v_code_2361_);
v_a_2477_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2448_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2448_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_decl_2437_);
lean_dec_ref(v_code_2361_);
return v___x_2445_;
}
}
v___jp_2485_:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v___y_2435_ = v___y_2486_;
v___y_2436_ = v___y_2487_;
v_decl_2437_ = v_a_2497_;
v___y_2438_ = v___y_2489_;
v___y_2439_ = v___y_2490_;
v___y_2440_ = v___y_2491_;
v___y_2441_ = v___y_2492_;
v___y_2442_ = v___y_2493_;
v___y_2443_ = v___y_2494_;
v___y_2444_ = v___y_2495_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v_code_2361_);
v_a_2498_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2496_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
v___jp_2506_:
{
lean_object* v_fvarId_2516_; lean_object* v_params_2517_; lean_object* v_type_2518_; lean_object* v___x_2519_; 
v_fvarId_2516_ = lean_ctor_get(v_decl_2507_, 0);
v_params_2517_ = lean_ctor_get(v_decl_2507_, 2);
v_type_2518_ = lean_ctor_get(v_decl_2507_, 3);
v___x_2519_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2516_, v___y_2510_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; uint8_t v___x_2521_; uint8_t v___x_2522_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = 0;
v___x_2522_ = lean_unbox(v_a_2520_);
if (v___x_2522_ == 0)
{
uint8_t v___x_2523_; 
v___x_2523_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2361_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
v___y_2486_ = v___x_2524_;
v___y_2487_ = v_k_2508_;
v_decl_2488_ = v_decl_2507_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
v___y_2491_ = v___y_2511_;
v___y_2492_ = v___y_2512_;
v___y_2493_ = v___y_2513_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2515_;
goto v___jp_2485_;
}
else
{
uint8_t v___x_2525_; 
lean_inc_ref(v_type_2518_);
v___x_2525_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2518_, v_params_2517_);
if (v___x_2525_ == 0)
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
v___y_2486_ = v___x_2526_;
v___y_2487_ = v_k_2508_;
v_decl_2488_ = v_decl_2507_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
v___y_2491_ = v___y_2511_;
v___y_2492_ = v___y_2512_;
v___y_2493_ = v___y_2513_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2515_;
goto v___jp_2485_;
}
else
{
lean_object* v___x_2527_; lean_object* v_subst_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = lean_st_ref_get(v___y_2510_);
v_subst_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_subst_2528_);
lean_dec(v___x_2527_);
v___x_2529_ = lean_unbox(v_a_2520_);
v___x_2530_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2521_, v___x_2529_, v_decl_2507_, v_subst_2528_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec_ref(v_subst_2528_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2531_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2510_);
if (lean_obj_tag(v___x_2534_) == 0)
{
uint8_t v___x_2535_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2535_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
v___y_2486_ = v___x_2535_;
v___y_2487_ = v_k_2508_;
v_decl_2488_ = v_a_2533_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
v___y_2491_ = v___y_2511_;
v___y_2492_ = v___y_2512_;
v___y_2493_ = v___y_2513_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2515_;
goto v___jp_2485_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2533_);
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_k_2508_);
lean_dec_ref(v_code_2361_);
v_a_2536_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2534_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2534_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_k_2508_);
lean_dec_ref(v_code_2361_);
v_a_2544_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2532_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2532_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_k_2508_);
lean_dec_ref(v_code_2361_);
v_a_2552_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2530_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2530_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
else
{
lean_object* v___x_2560_; lean_object* v_subst_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2560_ = lean_st_ref_get(v___y_2510_);
v_subst_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_subst_2561_);
lean_dec(v___x_2560_);
v___x_2562_ = 0;
v___x_2563_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2521_, v___x_2562_, v_decl_2507_, v_subst_2561_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec_ref(v_subst_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; uint8_t v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
v___y_2435_ = v___x_2565_;
v___y_2436_ = v_k_2508_;
v_decl_2437_ = v_a_2564_;
v___y_2438_ = v___y_2509_;
v___y_2439_ = v___y_2510_;
v___y_2440_ = v___y_2511_;
v___y_2441_ = v___y_2512_;
v___y_2442_ = v___y_2513_;
v___y_2443_ = v___y_2514_;
v___y_2444_ = v___y_2515_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_k_2508_);
lean_dec_ref(v_code_2361_);
v_a_2566_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2563_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_k_2508_);
lean_dec_ref(v_decl_2507_);
lean_dec_ref(v_code_2361_);
v_a_2574_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2519_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2519_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
v___jp_2582_:
{
lean_object* v___x_2593_; 
lean_inc_ref(v___y_2586_);
v___x_2593_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2586_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
if (lean_obj_tag(v_a_2594_) == 1)
{
lean_object* v_val_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_val_2595_ = lean_ctor_get(v_a_2594_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v_a_2594_, 1);
v___x_2596_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2592_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2596_, 1);
lean_inc_ref(v___y_2587_);
v___x_2597_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2591_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2595_, v_a_2598_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
lean_dec_ref(v___y_2587_);
lean_dec(v_val_2595_);
return v___x_2599_;
}
else
{
lean_dec(v_val_2595_);
lean_dec_ref(v___y_2587_);
return v___x_2597_;
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_val_2595_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2587_);
v_a_2600_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2596_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2596_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2608_; 
lean_dec(v_a_2594_);
lean_inc_ref(v___y_2586_);
v___x_2608_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2586_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
if (lean_obj_tag(v_a_2609_) == 1)
{
lean_object* v_val_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_val_2610_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_a_2609_, 1);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_val_2610_);
lean_ctor_set(v___x_2611_, 1, v___y_2591_);
v_code_2361_ = v___x_2611_;
v_a_2362_ = v___y_2584_;
v_a_2363_ = v___y_2592_;
v_a_2364_ = v___y_2588_;
v_a_2365_ = v___y_2583_;
v_a_2366_ = v___y_2589_;
v_a_2367_ = v___y_2587_;
v_a_2368_ = v___y_2585_;
goto _start;
}
else
{
lean_object* v_fvarId_2613_; lean_object* v_value_2614_; lean_object* v___x_2615_; 
lean_dec(v_a_2609_);
v_fvarId_2613_ = lean_ctor_get(v___y_2586_, 0);
v_value_2614_ = lean_ctor_get(v___y_2586_, 3);
v___x_2615_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2614_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
if (lean_obj_tag(v_a_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v___x_2618_; 
lean_dec_ref(v___y_2590_);
lean_dec_ref(v_code_2361_);
v_val_2617_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v_a_2616_, 1);
lean_inc(v_fvarId_2613_);
v___x_2618_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2613_, v_val_2617_, v___y_2592_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2618_, 1);
v___x_2619_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2586_, v___y_2592_, v___y_2589_);
lean_dec_ref(v___y_2586_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_dec_ref_known(v___x_2619_, 1);
v_code_2361_ = v___y_2591_;
v_a_2362_ = v___y_2584_;
v_a_2363_ = v___y_2592_;
v_a_2364_ = v___y_2588_;
v_a_2365_ = v___y_2583_;
v_a_2366_ = v___y_2589_;
v_a_2367_ = v___y_2587_;
v_a_2368_ = v___y_2585_;
goto _start;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2587_);
v_a_2621_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2619_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2619_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
v_a_2629_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2618_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2618_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v___x_2637_; 
lean_dec(v_a_2616_);
lean_inc_ref(v___y_2591_);
lean_inc_ref(v___y_2586_);
v___x_2637_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2586_, v___y_2591_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
if (lean_obj_tag(v_a_2638_) == 1)
{
lean_object* v_val_2639_; lean_object* v___x_2640_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v_code_2361_);
v_val_2639_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v_a_2638_, 1);
v___x_2640_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2586_, v___y_2592_, v___y_2589_);
lean_dec_ref(v___y_2586_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2648_);
v___x_2642_ = v___x_2640_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v___x_2640_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_val_2639_);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_val_2639_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_val_2639_);
v_a_2649_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2640_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2640_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v___x_2657_; 
lean_dec(v_a_2638_);
lean_inc(v_value_2614_);
v___x_2657_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2614_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
if (lean_obj_tag(v_a_2658_) == 1)
{
lean_object* v_val_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v___x_2662_; 
lean_dec_ref(v___y_2590_);
lean_dec_ref(v_code_2361_);
v_val_2659_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_val_2659_);
lean_dec_ref_known(v_a_2658_, 1);
v_fst_2660_ = lean_ctor_get(v_val_2659_, 0);
lean_inc(v_fst_2660_);
v_snd_2661_ = lean_ctor_get(v_val_2659_, 1);
lean_inc(v_snd_2661_);
lean_dec(v_val_2659_);
lean_inc(v_fvarId_2613_);
v___x_2662_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2613_, v_snd_2661_, v___y_2592_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref_known(v___x_2662_, 1);
v___x_2663_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2586_, v___y_2592_, v___y_2589_);
lean_dec_ref(v___y_2586_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref_known(v___x_2663_, 1);
lean_inc_ref(v___y_2587_);
v___x_2664_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2591_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2660_, v_a_2665_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
lean_dec_ref(v___y_2587_);
lean_dec(v_fst_2660_);
return v___x_2666_;
}
else
{
lean_dec(v_fst_2660_);
lean_dec_ref(v___y_2587_);
return v___x_2664_;
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_fst_2660_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2587_);
v_a_2667_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2663_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_fst_2660_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
v_a_2675_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2662_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2662_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v_a_2658_);
lean_inc_ref(v___y_2587_);
lean_inc_ref(v___y_2591_);
v___x_2683_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2591_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2613_, v___y_2592_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; uint8_t v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_unbox(v_a_2686_);
lean_dec(v_a_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v_code_2361_);
v___x_2688_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2586_, v___y_2592_, v___y_2589_);
lean_dec_ref(v___y_2586_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2688_, 0);
lean_dec(v_unused_2696_);
v___x_2690_ = v___x_2688_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v___x_2688_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v_a_2684_);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2684_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2684_);
v_a_2697_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2688_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2688_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v___x_2705_; 
lean_inc_ref(v___y_2586_);
v___x_2705_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2586_, v___y_2584_, v___y_2592_, v___y_2588_, v___y_2583_, v___y_2589_, v___y_2587_, v___y_2585_);
lean_dec_ref(v___y_2587_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2726_; 
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2705_, 0);
lean_dec(v_unused_2727_);
v___x_2707_ = v___x_2705_;
v_isShared_2708_ = v_isSharedCheck_2726_;
goto v_resetjp_2706_;
}
else
{
lean_dec(v___x_2705_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2726_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
size_t v___x_2709_; size_t v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = lean_ptr_addr(v___y_2591_);
lean_dec_ref(v___y_2591_);
v___x_2710_ = lean_ptr_addr(v_a_2684_);
v___x_2711_ = lean_usize_dec_eq(v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec_ref(v___y_2590_);
lean_dec_ref(v_code_2361_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___y_2586_);
lean_ctor_set(v___x_2712_, 1, v_a_2684_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2712_);
v___x_2714_ = v___x_2707_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
else
{
size_t v___x_2716_; size_t v___x_2717_; uint8_t v___x_2718_; 
v___x_2716_ = lean_ptr_addr(v___y_2590_);
lean_dec_ref(v___y_2590_);
v___x_2717_ = lean_ptr_addr(v___y_2586_);
v___x_2718_ = lean_usize_dec_eq(v___x_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec_ref(v_code_2361_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___y_2586_);
lean_ctor_set(v___x_2719_, 1, v_a_2684_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2719_);
v___x_2721_ = v___x_2707_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
lean_object* v___x_2724_; 
lean_dec(v_a_2684_);
lean_dec_ref(v___y_2586_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v_code_2361_);
v___x_2724_ = v___x_2707_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_code_2361_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2684_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2728_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2705_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2705_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2684_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2736_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2685_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2685_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
return v___x_2683_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2744_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2657_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2657_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2752_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2637_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2637_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2760_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2615_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2615_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2768_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2608_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2608_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v_code_2361_);
v_a_2776_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2593_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2593_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
v___jp_2784_:
{
uint8_t v___x_2799_; 
v___x_2799_ = l_Lean_Expr_isErased(v_type_2790_);
lean_dec_ref(v_type_2790_);
if (v___x_2799_ == 0)
{
lean_dec(v_value_2791_);
lean_dec(v_fvarId_2789_);
v___y_2583_ = v___y_2795_;
v___y_2584_ = v___y_2792_;
v___y_2585_ = v___y_2798_;
v___y_2586_ = v_decl_2788_;
v___y_2587_ = v___y_2797_;
v___y_2588_ = v___y_2794_;
v___y_2589_ = v___y_2796_;
v___y_2590_ = v___y_2787_;
v___y_2591_ = v___y_2786_;
v___y_2592_ = v___y_2793_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = lean_box(1);
v___x_2801_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2785_, v_value_2791_, v___x_2800_);
lean_dec(v_value_2791_);
if (v___x_2801_ == 0)
{
if (v___x_2799_ == 0)
{
lean_dec(v_fvarId_2789_);
v___y_2583_ = v___y_2795_;
v___y_2584_ = v___y_2792_;
v___y_2585_ = v___y_2798_;
v___y_2586_ = v_decl_2788_;
v___y_2587_ = v___y_2797_;
v___y_2588_ = v___y_2794_;
v___y_2589_ = v___y_2796_;
v___y_2590_ = v___y_2787_;
v___y_2591_ = v___y_2786_;
v___y_2592_ = v___y_2793_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2802_; lean_object* v_subst_2803_; lean_object* v_used_2804_; lean_object* v_binderRenaming_2805_; lean_object* v_funDeclInfoMap_2806_; uint8_t v_simplified_2807_; lean_object* v_visited_2808_; lean_object* v_inline_2809_; lean_object* v_inlineLocal_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v___y_2787_);
lean_dec_ref(v_code_2361_);
v___x_2802_ = lean_st_ref_take(v___y_2793_);
v_subst_2803_ = lean_ctor_get(v___x_2802_, 0);
v_used_2804_ = lean_ctor_get(v___x_2802_, 1);
v_binderRenaming_2805_ = lean_ctor_get(v___x_2802_, 2);
v_funDeclInfoMap_2806_ = lean_ctor_get(v___x_2802_, 3);
v_simplified_2807_ = lean_ctor_get_uint8(v___x_2802_, sizeof(void*)*7);
v_visited_2808_ = lean_ctor_get(v___x_2802_, 4);
v_inline_2809_ = lean_ctor_get(v___x_2802_, 5);
v_inlineLocal_2810_ = lean_ctor_get(v___x_2802_, 6);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2812_ = v___x_2802_;
v_isShared_2813_ = v_isSharedCheck_2830_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_inlineLocal_2810_);
lean_inc(v_inline_2809_);
lean_inc(v_visited_2808_);
lean_inc(v_funDeclInfoMap_2806_);
lean_inc(v_binderRenaming_2805_);
lean_inc(v_used_2804_);
lean_inc(v_subst_2803_);
lean_dec(v___x_2802_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2830_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2803_, v_fvarId_2789_, v___x_2814_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2815_);
v___x_2817_ = v___x_2812_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_used_2804_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_binderRenaming_2805_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_funDeclInfoMap_2806_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_visited_2808_);
lean_ctor_set(v_reuseFailAlloc_2829_, 5, v_inline_2809_);
lean_ctor_set(v_reuseFailAlloc_2829_, 6, v_inlineLocal_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2829_, sizeof(void*)*7, v_simplified_2807_);
v___x_2817_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_st_ref_put(v___y_2793_, v___x_2817_);
v___x_2819_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2788_, v___y_2793_, v___y_2796_);
lean_dec_ref(v_decl_2788_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec_ref_known(v___x_2819_, 1);
v_code_2361_ = v___y_2786_;
v_a_2362_ = v___y_2792_;
v_a_2363_ = v___y_2793_;
v_a_2364_ = v___y_2794_;
v_a_2365_ = v___y_2795_;
v_a_2366_ = v___y_2796_;
v_a_2367_ = v___y_2797_;
v_a_2368_ = v___y_2798_;
goto _start;
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v___y_2797_);
lean_dec_ref(v___y_2786_);
v_a_2821_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2789_);
v___y_2583_ = v___y_2795_;
v___y_2584_ = v___y_2792_;
v___y_2585_ = v___y_2798_;
v___y_2586_ = v_decl_2788_;
v___y_2587_ = v___y_2797_;
v___y_2588_ = v___y_2794_;
v___y_2589_ = v___y_2796_;
v___y_2590_ = v___y_2787_;
v___y_2591_ = v___y_2786_;
v___y_2592_ = v___y_2793_;
goto v___jp_2582_;
}
}
}
v___jp_2831_:
{
lean_object* v_fvarId_2843_; lean_object* v_type_2844_; lean_object* v_value_2845_; lean_object* v___x_2846_; 
v_fvarId_2843_ = lean_ctor_get(v___y_2833_, 0);
v_type_2844_ = lean_ctor_get(v___y_2833_, 2);
v_value_2845_ = lean_ctor_get(v___y_2833_, 3);
lean_inc(v_value_2845_);
v___x_2846_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2845_, v___y_2836_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
if (lean_obj_tag(v_a_2847_) == 1)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; 
v_val_2848_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v_a_2847_, 1);
v___x_2849_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2837_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
lean_dec_ref_known(v___x_2849_, 1);
v___x_2850_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2832_, v___y_2833_, v_val_2848_, v___y_2840_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_fvarId_2852_; lean_object* v_type_2853_; lean_object* v_value_2854_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v_fvarId_2852_ = lean_ctor_get(v_a_2851_, 0);
lean_inc(v_fvarId_2852_);
v_type_2853_ = lean_ctor_get(v_a_2851_, 2);
lean_inc_ref(v_type_2853_);
v_value_2854_ = lean_ctor_get(v_a_2851_, 3);
lean_inc(v_value_2854_);
v___y_2785_ = v___y_2832_;
v___y_2786_ = v___y_2835_;
v___y_2787_ = v___y_2834_;
v_decl_2788_ = v_a_2851_;
v_fvarId_2789_ = v_fvarId_2852_;
v_type_2790_ = v_type_2853_;
v_value_2791_ = v_value_2854_;
v___y_2792_ = v___y_2836_;
v___y_2793_ = v___y_2837_;
v___y_2794_ = v___y_2838_;
v___y_2795_ = v___y_2839_;
v___y_2796_ = v___y_2840_;
v___y_2797_ = v___y_2841_;
v___y_2798_ = v___y_2842_;
goto v___jp_2784_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v___y_2841_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_code_2361_);
v_a_2855_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2850_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2850_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_val_2848_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v_code_2361_);
v_a_2863_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2849_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2849_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_inc(v_value_2845_);
lean_inc_ref(v_type_2844_);
lean_inc(v_fvarId_2843_);
lean_dec(v_a_2847_);
v___y_2785_ = v___y_2832_;
v___y_2786_ = v___y_2835_;
v___y_2787_ = v___y_2834_;
v_decl_2788_ = v___y_2833_;
v_fvarId_2789_ = v_fvarId_2843_;
v_type_2790_ = v_type_2844_;
v_value_2791_ = v_value_2845_;
v___y_2792_ = v___y_2836_;
v___y_2793_ = v___y_2837_;
v___y_2794_ = v___y_2838_;
v___y_2795_ = v___y_2839_;
v___y_2796_ = v___y_2840_;
v___y_2797_ = v___y_2841_;
v___y_2798_ = v___y_2842_;
goto v___jp_2784_;
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v___y_2841_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v_code_2361_);
v_a_2871_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2846_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2846_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
v___jp_2879_:
{
if (v___y_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v_code_2361_);
v___x_2883_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2881_);
lean_ctor_set(v___x_2883_, 1, v___y_2880_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; 
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_code_2361_);
return v___x_2885_;
}
}
v___jp_2886_:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_Lean_instBEqFVarId_beq(v___y_2889_, v___y_2890_);
lean_dec(v___y_2889_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v___y_2888_);
v___y_2880_ = v___y_2887_;
v___y_2881_ = v___y_2890_;
v___y_2882_ = v___x_2891_;
goto v___jp_2879_;
}
else
{
size_t v___x_2892_; size_t v___x_2893_; uint8_t v___x_2894_; 
v___x_2892_ = lean_ptr_addr(v___y_2888_);
lean_dec_ref(v___y_2888_);
v___x_2893_ = lean_ptr_addr(v___y_2887_);
v___x_2894_ = lean_usize_dec_eq(v___x_2892_, v___x_2893_);
v___y_2880_ = v___y_2887_;
v___y_2881_ = v___y_2890_;
v___y_2882_ = v___x_2894_;
goto v___jp_2879_;
}
}
v___jp_2895_:
{
if (lean_obj_tag(v___y_2900_) == 0)
{
lean_dec_ref_known(v___y_2900_, 1);
v___y_2887_ = v___y_2896_;
v___y_2888_ = v___y_2897_;
v___y_2889_ = v___y_2899_;
v___y_2890_ = v___y_2898_;
goto v___jp_2886_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec_ref(v_code_2361_);
v_a_2901_ = lean_ctor_get(v___y_2900_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___y_2900_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___y_2900_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___y_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
v___jp_2909_:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2911_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2921_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___y_2910_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v___y_2910_);
v_a_2922_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2912_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
v___jp_2930_:
{
if (lean_obj_tag(v___y_2933_) == 0)
{
lean_dec_ref_known(v___y_2933_, 1);
v___y_2910_ = v___y_2931_;
v___y_2911_ = v___y_2932_;
goto v___jp_2909_;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___y_2931_);
v_a_2934_ = lean_ctor_get(v___y_2933_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___y_2933_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___y_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___y_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_nat_dec_lt(v___y_2951_, v___y_2945_);
lean_dec(v___y_2951_);
if (v___x_2952_ == 0)
{
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2943_);
v___y_2910_ = v___y_2946_;
v___y_2911_ = v___y_2947_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_nat_dec_le(v___y_2945_, v___y_2945_);
if (v___x_2954_ == 0)
{
if (v___x_2952_ == 0)
{
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2943_);
v___y_2910_ = v___y_2946_;
v___y_2911_ = v___y_2947_;
goto v___jp_2909_;
}
else
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = ((size_t)0ULL);
v___x_2956_ = lean_usize_of_nat(v___y_2945_);
lean_dec(v___y_2945_);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2943_, v___x_2955_, v___x_2956_, v___x_2953_, v___y_2949_, v___y_2944_, v___y_2948_, v___y_2950_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2943_);
v___y_2931_ = v___y_2946_;
v___y_2932_ = v___y_2947_;
v___y_2933_ = v___x_2957_;
goto v___jp_2930_;
}
}
else
{
size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = lean_usize_of_nat(v___y_2945_);
lean_dec(v___y_2945_);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2943_, v___x_2958_, v___x_2959_, v___x_2953_, v___y_2949_, v___y_2944_, v___y_2948_, v___y_2950_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2943_);
v___y_2931_ = v___y_2946_;
v___y_2932_ = v___y_2947_;
v___y_2933_ = v___x_2960_;
goto v___jp_2930_;
}
}
}
v___jp_2961_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2966_, 0, v___y_2963_);
lean_ctor_set(v___x_2966_, 1, v___y_2964_);
lean_ctor_set(v___x_2966_, 2, v___y_2965_);
lean_ctor_set(v___x_2966_, 3, v___y_2962_);
v___x_2967_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
v___jp_2969_:
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v___y_2970_);
v___x_2984_ = lean_nat_dec_lt(v___y_2977_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v_code_2361_);
v___y_2943_ = v___y_2970_;
v___y_2944_ = v___y_2980_;
v___y_2945_ = v___x_2983_;
v___y_2946_ = v___y_2975_;
v___y_2947_ = v___y_2978_;
v___y_2948_ = v___y_2981_;
v___y_2949_ = v___y_2979_;
v___y_2950_ = v___y_2982_;
v___y_2951_ = v___y_2977_;
goto v___jp_2942_;
}
else
{
if (v___x_2984_ == 0)
{
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v_code_2361_);
v___y_2943_ = v___y_2970_;
v___y_2944_ = v___y_2980_;
v___y_2945_ = v___x_2983_;
v___y_2946_ = v___y_2975_;
v___y_2947_ = v___y_2978_;
v___y_2948_ = v___y_2981_;
v___y_2949_ = v___y_2979_;
v___y_2950_ = v___y_2982_;
v___y_2951_ = v___y_2977_;
goto v___jp_2942_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; uint8_t v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___x_2983_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2970_, v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec(v___y_2976_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v_code_2361_);
v___y_2943_ = v___y_2970_;
v___y_2944_ = v___y_2980_;
v___y_2945_ = v___x_2983_;
v___y_2946_ = v___y_2975_;
v___y_2947_ = v___y_2978_;
v___y_2948_ = v___y_2981_;
v___y_2949_ = v___y_2979_;
v___y_2950_ = v___y_2982_;
v___y_2951_ = v___y_2977_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2988_; 
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2977_);
lean_inc(v___y_2976_);
v___x_2988_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2976_, v___y_2978_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3002_; 
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_3003_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_3002_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3002_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
size_t v___x_2992_; size_t v___x_2993_; uint8_t v___x_2994_; 
v___x_2992_ = lean_ptr_addr(v___y_2972_);
lean_dec_ref(v___y_2972_);
v___x_2993_ = lean_ptr_addr(v___y_2970_);
v___x_2994_ = lean_usize_dec_eq(v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_del_object(v___x_2990_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2971_);
lean_dec_ref(v_code_2361_);
v___y_2962_ = v___y_2970_;
v___y_2963_ = v___y_2974_;
v___y_2964_ = v___y_2975_;
v___y_2965_ = v___y_2976_;
goto v___jp_2961_;
}
else
{
size_t v___x_2995_; size_t v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_ptr_addr(v___y_2973_);
lean_dec_ref(v___y_2973_);
v___x_2996_ = lean_ptr_addr(v___y_2975_);
v___x_2997_ = lean_usize_dec_eq(v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_del_object(v___x_2990_);
lean_dec(v___y_2971_);
lean_dec_ref(v_code_2361_);
v___y_2962_ = v___y_2970_;
v___y_2963_ = v___y_2974_;
v___y_2964_ = v___y_2975_;
v___y_2965_ = v___y_2976_;
goto v___jp_2961_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_instBEqFVarId_beq(v___y_2971_, v___y_2976_);
lean_dec(v___y_2971_);
if (v___x_2998_ == 0)
{
lean_del_object(v___x_2990_);
lean_dec_ref(v_code_2361_);
v___y_2962_ = v___y_2970_;
v___y_2963_ = v___y_2974_;
v___y_2964_ = v___y_2975_;
v___y_2965_ = v___y_2976_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_3000_; 
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2970_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v_code_2361_);
v___x_3000_ = v___x_2990_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_code_2361_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v_code_2361_);
v_a_3004_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2988_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2988_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
}
v___jp_3012_:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3013_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3015_, 0);
lean_dec(v_unused_3023_);
v___x_3017_ = v___x_3015_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_dec(v___x_3015_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___y_3014_);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___y_3014_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v___y_3014_);
v_a_3024_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3015_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
v___jp_3032_:
{
if (lean_obj_tag(v___y_3035_) == 0)
{
lean_dec_ref_known(v___y_3035_, 1);
v___y_3013_ = v___y_3033_;
v___y_3014_ = v___y_3034_;
goto v___jp_3012_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___y_3034_);
v_a_3036_ = lean_ctor_get(v___y_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___y_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___y_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___y_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
v___jp_3044_:
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_lt(v___y_3050_, v___y_3049_);
lean_dec(v___y_3050_);
if (v___x_3051_ == 0)
{
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3046_);
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___y_3048_;
goto v___jp_3012_;
}
else
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_nat_dec_le(v___y_3049_, v___y_3049_);
if (v___x_3053_ == 0)
{
if (v___x_3051_ == 0)
{
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3046_);
v___y_3013_ = v___y_3047_;
v___y_3014_ = v___y_3048_;
goto v___jp_3012_;
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_of_nat(v___y_3049_);
lean_dec(v___y_3049_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3046_, v___x_3054_, v___x_3055_, v___x_3052_, v___y_3045_);
lean_dec_ref(v___y_3046_);
v___y_3033_ = v___y_3047_;
v___y_3034_ = v___y_3048_;
v___y_3035_ = v___x_3056_;
goto v___jp_3032_;
}
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___y_3049_);
lean_dec(v___y_3049_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3046_, v___x_3057_, v___x_3058_, v___x_3052_, v___y_3045_);
lean_dec_ref(v___y_3046_);
v___y_3033_ = v___y_3047_;
v___y_3034_ = v___y_3048_;
v___y_3035_ = v___x_3059_;
goto v___jp_3032_;
}
}
}
v___jp_3060_:
{
switch(lean_obj_tag(v_code_2361_))
{
case 0:
{
lean_object* v_decl_3068_; lean_object* v_k_3069_; uint8_t v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
v_decl_3068_ = lean_ctor_get(v_code_2361_, 0);
v_k_3069_ = lean_ctor_get(v_code_2361_, 1);
v___x_3070_ = 0;
v___x_3071_ = 0;
lean_inc_ref(v_decl_3068_);
v___x_3072_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3070_, v___x_3071_, v_decl_3068_, v___y_3062_, v___y_3065_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; uint8_t v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3070_, v_decl_3068_, v_a_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3062_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_dec_ref_known(v___x_3075_, 1);
lean_inc_ref(v_k_3069_);
lean_inc_ref(v_decl_3068_);
v___y_2832_ = v___x_3070_;
v___y_2833_ = v_a_3073_;
v___y_2834_ = v_decl_3068_;
v___y_2835_ = v_k_3069_;
v___y_2836_ = v___y_3061_;
v___y_2837_ = v___y_3062_;
v___y_2838_ = v___y_3063_;
v___y_2839_ = v___y_3064_;
v___y_2840_ = v___y_3065_;
v___y_2841_ = v___y_3066_;
v___y_2842_ = v___y_3067_;
goto v___jp_2831_;
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3073_);
lean_dec_ref_known(v_code_2361_, 2);
lean_dec_ref(v___y_3066_);
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_inc_ref(v_k_3069_);
lean_inc_ref(v_decl_3068_);
v___y_2832_ = v___x_3070_;
v___y_2833_ = v_a_3073_;
v___y_2834_ = v_decl_3068_;
v___y_2835_ = v_k_3069_;
v___y_2836_ = v___y_3061_;
v___y_2837_ = v___y_3062_;
v___y_2838_ = v___y_3063_;
v___y_2839_ = v___y_3064_;
v___y_2840_ = v___y_3065_;
v___y_2841_ = v___y_3066_;
v___y_2842_ = v___y_3067_;
goto v___jp_2831_;
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref_known(v_code_2361_, 2);
lean_dec_ref(v___y_3066_);
v_a_3084_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3072_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3072_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3092_; lean_object* v_args_3093_; lean_object* v___x_3094_; lean_object* v_subst_3095_; uint8_t v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; 
v_fvarId_3092_ = lean_ctor_get(v_code_2361_, 0);
v_args_3093_ = lean_ctor_get(v_code_2361_, 1);
v___x_3094_ = lean_st_ref_get(v___y_3062_);
v_subst_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_ref(v_subst_3095_);
lean_dec(v___x_3094_);
v___x_3096_ = 0;
v___x_3097_ = 0;
lean_inc(v_fvarId_3092_);
v___x_3098_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3095_, v_fvarId_3092_, v___x_3097_);
lean_dec_ref(v_subst_3095_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_fvarId_3099_; lean_object* v___x_3100_; 
v_fvarId_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_fvarId_3099_);
lean_dec_ref_known(v___x_3098_, 1);
lean_inc_ref(v_args_3093_);
v___x_3100_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3096_, v___x_3097_, v_args_3093_, v___y_3062_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_n(v_a_3101_, 2);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3099_, v_a_3101_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
if (lean_obj_tag(v_a_3103_) == 1)
{
lean_object* v_val_3104_; 
lean_dec(v_a_3101_);
lean_dec(v_fvarId_3099_);
lean_dec_ref_known(v_code_2361_, 2);
v_val_3104_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v_a_3103_, 1);
v_code_2361_ = v_val_3104_;
v_a_2362_ = v___y_3061_;
v_a_2363_ = v___y_3062_;
v_a_2364_ = v___y_3063_;
v_a_2365_ = v___y_3064_;
v_a_2366_ = v___y_3065_;
v_a_2367_ = v___y_3066_;
v_a_2368_ = v___y_3067_;
goto _start;
}
else
{
lean_object* v___x_3106_; 
lean_dec(v_a_3103_);
lean_dec_ref(v___y_3066_);
lean_inc(v_fvarId_3099_);
v___x_3106_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3099_, v___y_3062_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
lean_dec_ref_known(v___x_3106_, 1);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_array_get_size(v_a_3101_);
v___x_3109_ = lean_nat_dec_lt(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_inc(v_fvarId_3092_);
lean_inc_ref(v_args_3093_);
v___y_2887_ = v_a_3101_;
v___y_2888_ = v_args_3093_;
v___y_2889_ = v_fvarId_3092_;
v___y_2890_ = v_fvarId_3099_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_nat_dec_le(v___x_3108_, v___x_3108_);
if (v___x_3111_ == 0)
{
if (v___x_3109_ == 0)
{
lean_inc(v_fvarId_3092_);
lean_inc_ref(v_args_3093_);
v___y_2887_ = v_a_3101_;
v___y_2888_ = v_args_3093_;
v___y_2889_ = v_fvarId_3092_;
v___y_2890_ = v_fvarId_3099_;
goto v___jp_2886_;
}
else
{
size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((size_t)0ULL);
v___x_3113_ = lean_usize_of_nat(v___x_3108_);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3101_, v___x_3112_, v___x_3113_, v___x_3110_, v___y_3062_);
lean_inc(v_fvarId_3092_);
lean_inc_ref(v_args_3093_);
v___y_2896_ = v_a_3101_;
v___y_2897_ = v_args_3093_;
v___y_2898_ = v_fvarId_3099_;
v___y_2899_ = v_fvarId_3092_;
v___y_2900_ = v___x_3114_;
goto v___jp_2895_;
}
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = lean_usize_of_nat(v___x_3108_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3101_, v___x_3115_, v___x_3116_, v___x_3110_, v___y_3062_);
lean_inc(v_fvarId_3092_);
lean_inc_ref(v_args_3093_);
v___y_2896_ = v_a_3101_;
v___y_2897_ = v_args_3093_;
v___y_2898_ = v_fvarId_3099_;
v___y_2899_ = v_fvarId_3092_;
v___y_2900_ = v___x_3117_;
goto v___jp_2895_;
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_3101_);
lean_dec(v_fvarId_3099_);
lean_dec_ref_known(v_code_2361_, 2);
v_a_3118_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3106_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3106_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_a_3101_);
lean_dec(v_fvarId_3099_);
lean_dec_ref_known(v_code_2361_, 2);
lean_dec_ref(v___y_3066_);
v_a_3126_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3102_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3102_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_fvarId_3099_);
lean_dec_ref_known(v_code_2361_, 2);
lean_dec_ref(v___y_3066_);
v_a_3134_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3100_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3100_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v___x_3142_; 
lean_dec_ref_known(v_code_2361_, 2);
v___x_3142_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3096_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec_ref(v___y_3066_);
return v___x_3142_;
}
}
case 4:
{
lean_object* v_cases_3143_; lean_object* v___x_3144_; 
v_cases_3143_ = lean_ctor_get(v_code_2361_, 0);
lean_inc_ref(v_cases_3143_);
v___x_3144_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3143_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3217_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3217_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3217_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
if (lean_obj_tag(v_a_3145_) == 1)
{
lean_object* v_val_3149_; lean_object* v___x_3151_; 
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_val_3149_ = lean_ctor_get(v_a_3145_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v_a_3145_, 1);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_val_3149_);
v___x_3151_ = v___x_3147_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_val_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
else
{
lean_object* v_typeName_3153_; lean_object* v_resultType_3154_; lean_object* v_discr_3155_; lean_object* v_alts_3156_; lean_object* v___x_3157_; lean_object* v_subst_3158_; uint8_t v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; 
lean_del_object(v___x_3147_);
lean_dec(v_a_3145_);
v_typeName_3153_ = lean_ctor_get(v_cases_3143_, 0);
v_resultType_3154_ = lean_ctor_get(v_cases_3143_, 1);
v_discr_3155_ = lean_ctor_get(v_cases_3143_, 2);
v_alts_3156_ = lean_ctor_get(v_cases_3143_, 3);
v___x_3157_ = lean_st_ref_get(v___y_3062_);
v_subst_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc_ref(v_subst_3158_);
lean_dec(v___x_3157_);
v___x_3159_ = 0;
v___x_3160_ = 0;
lean_inc(v_discr_3155_);
v___x_3161_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3158_, v_discr_3155_, v___x_3160_);
lean_dec_ref(v_subst_3158_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_fvarId_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_fvarId_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc_n(v_fvarId_3162_, 2);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = lean_st_ref_get(v___y_3062_);
v___x_3164_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3156_);
v___x_3165_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3162_, v___x_3164_, v_alts_3156_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3166_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3199_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3199_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3199_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_subst_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_subst_3172_ = lean_ctor_get(v___x_3163_, 0);
lean_inc_ref(v_subst_3172_);
lean_dec(v___x_3163_);
lean_inc_ref(v_resultType_3154_);
v___x_3173_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3159_, v_subst_3172_, v___x_3160_, v_resultType_3154_);
lean_dec_ref(v_subst_3172_);
v___x_3174_ = lean_array_get_size(v_a_3168_);
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = lean_nat_dec_eq(v___x_3174_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_del_object(v___x_3170_);
lean_inc(v_typeName_3153_);
lean_inc_ref(v_resultType_3154_);
lean_inc_ref(v_alts_3156_);
lean_inc(v_discr_3155_);
v___y_2970_ = v_a_3168_;
v___y_2971_ = v_discr_3155_;
v___y_2972_ = v_alts_3156_;
v___y_2973_ = v_resultType_3154_;
v___y_2974_ = v_typeName_3153_;
v___y_2975_ = v___x_3173_;
v___y_2976_ = v_fvarId_3162_;
v___y_2977_ = v___x_3164_;
v___y_2978_ = v___y_3062_;
v___y_2979_ = v___y_3064_;
v___y_2980_ = v___y_3065_;
v___y_2981_ = v___y_3066_;
v___y_2982_ = v___y_3067_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_array_fget_borrowed(v_a_3168_, v___x_3164_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_params_3178_; lean_object* v_code_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
lean_del_object(v___x_3170_);
v_params_3178_ = lean_ctor_get(v___x_3177_, 1);
v_code_3179_ = lean_ctor_get(v___x_3177_, 2);
v___x_3180_ = lean_array_get_size(v_params_3178_);
v___x_3181_ = lean_nat_dec_lt(v___x_3164_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_inc_ref(v_code_3179_);
lean_inc_ref(v_params_3178_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v___y_3045_ = v___y_3065_;
v___y_3046_ = v_params_3178_;
v___y_3047_ = v___y_3062_;
v___y_3048_ = v_code_3179_;
v___y_3049_ = v___x_3180_;
v___y_3050_ = v___x_3164_;
goto v___jp_3044_;
}
else
{
if (v___x_3181_ == 0)
{
lean_inc_ref(v_code_3179_);
lean_inc_ref(v_params_3178_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v___y_3045_ = v___y_3065_;
v___y_3046_ = v_params_3178_;
v___y_3047_ = v___y_3062_;
v___y_3048_ = v_code_3179_;
v___y_3049_ = v___x_3180_;
v___y_3050_ = v___x_3164_;
goto v___jp_3044_;
}
else
{
size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = lean_usize_of_nat(v___x_3180_);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3178_, v___x_3182_, v___x_3183_, v___y_3062_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; uint8_t v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
if (v___x_3186_ == 0)
{
lean_inc_ref(v_code_3179_);
lean_inc_ref(v_params_3178_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v___y_3045_ = v___y_3065_;
v___y_3046_ = v_params_3178_;
v___y_3047_ = v___y_3062_;
v___y_3048_ = v_code_3179_;
v___y_3049_ = v___x_3180_;
v___y_3050_ = v___x_3164_;
goto v___jp_3044_;
}
else
{
lean_inc(v_typeName_3153_);
lean_inc_ref(v_resultType_3154_);
lean_inc_ref(v_alts_3156_);
lean_inc(v_discr_3155_);
v___y_2970_ = v_a_3168_;
v___y_2971_ = v_discr_3155_;
v___y_2972_ = v_alts_3156_;
v___y_2973_ = v_resultType_3154_;
v___y_2974_ = v_typeName_3153_;
v___y_2975_ = v___x_3173_;
v___y_2976_ = v_fvarId_3162_;
v___y_2977_ = v___x_3164_;
v___y_2978_ = v___y_3062_;
v___y_2979_ = v___y_3064_;
v___y_2980_ = v___y_3065_;
v___y_2981_ = v___y_3066_;
v___y_2982_ = v___y_3067_;
goto v___jp_2969_;
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_a_3187_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3184_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3184_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
else
{
lean_object* v_code_3195_; lean_object* v___x_3197_; 
lean_inc_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3168_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_code_3195_ = lean_ctor_get(v___x_3177_, 0);
lean_inc_ref(v_code_3195_);
lean_dec_ref_known(v___x_3177_, 1);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v_code_3195_);
v___x_3197_ = v___x_3170_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_code_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v___x_3163_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_a_3200_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3167_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3167_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v___x_3163_);
lean_dec(v_fvarId_3162_);
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_a_3208_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3165_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3165_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v___x_3216_; 
lean_dec_ref_known(v_code_2361_, 1);
v___x_3216_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3159_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec_ref(v___y_3066_);
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref_known(v_code_2361_, 1);
lean_dec_ref(v___y_3066_);
v_a_3218_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3144_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3144_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3226_; lean_object* v___x_3227_; lean_object* v_subst_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; 
v_fvarId_3226_ = lean_ctor_get(v_code_2361_, 0);
v___x_3227_ = lean_st_ref_get(v___y_3062_);
v_subst_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_subst_3228_);
lean_dec(v___x_3227_);
v___x_3229_ = 0;
lean_inc(v_fvarId_3226_);
v___x_3230_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3228_, v_fvarId_3226_, v___x_3229_);
lean_dec_ref(v_subst_3228_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_fvarId_3231_; lean_object* v___x_3232_; 
lean_dec_ref(v___y_3066_);
v_fvarId_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_n(v_fvarId_3231_, 2);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3231_, v___y_3062_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3252_);
v___x_3234_ = v___x_3232_;
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
else
{
lean_dec(v___x_3232_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
uint8_t v___x_3236_; 
v___x_3236_ = l_Lean_instBEqFVarId_beq(v_fvarId_3226_, v_fvarId_3231_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3246_; 
v_isSharedCheck_3246_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_3247_);
v___x_3238_ = v_code_2361_;
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
else
{
lean_dec(v_code_2361_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v_fvarId_3231_);
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_fvarId_3231_);
v___x_3241_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3241_);
v___x_3243_ = v___x_3234_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v___x_3249_; 
lean_dec(v_fvarId_3231_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_code_2361_);
v___x_3249_ = v___x_3234_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_code_2361_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_fvarId_3231_);
lean_dec_ref_known(v_code_2361_, 1);
v_a_3253_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3232_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3232_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
uint8_t v___x_3261_; lean_object* v___x_3262_; 
lean_dec_ref_known(v_code_2361_, 1);
v___x_3261_ = 0;
v___x_3262_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3261_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec_ref(v___y_3066_);
return v___x_3262_;
}
}
case 6:
{
lean_object* v_type_3263_; lean_object* v___x_3264_; lean_object* v_subst_3265_; uint8_t v___x_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; uint8_t v___x_3271_; 
lean_dec_ref(v___y_3066_);
v_type_3263_ = lean_ctor_get(v_code_2361_, 0);
v___x_3264_ = lean_st_ref_get(v___y_3062_);
v_subst_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc_ref(v_subst_3265_);
lean_dec(v___x_3264_);
v___x_3266_ = 0;
v___x_3267_ = 0;
lean_inc_ref(v_type_3263_);
v___x_3268_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3266_, v_subst_3265_, v___x_3267_, v_type_3263_);
lean_dec_ref(v_subst_3265_);
v___x_3269_ = lean_ptr_addr(v_type_3263_);
v___x_3270_ = lean_ptr_addr(v___x_3268_);
v___x_3271_ = lean_usize_dec_eq(v___x_3269_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v_code_2361_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v_code_2361_, 0);
lean_dec(v_unused_3280_);
v___x_3273_ = v_code_2361_;
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v_code_2361_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3268_);
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3268_);
v___x_3276_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
}
else
{
lean_object* v___x_3281_; 
lean_dec_ref(v___x_3268_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_code_2361_);
return v___x_3281_;
}
}
default: 
{
lean_object* v_decl_3282_; lean_object* v_k_3283_; 
v_decl_3282_ = lean_ctor_get(v_code_2361_, 0);
v_k_3283_ = lean_ctor_get(v_code_2361_, 1);
lean_inc_ref(v_k_3283_);
lean_inc_ref(v_decl_3282_);
v_decl_2507_ = v_decl_3282_;
v_k_2508_ = v_k_3283_;
v___y_2509_ = v___y_3061_;
v___y_2510_ = v___y_3062_;
v___y_2511_ = v___y_3063_;
v___y_2512_ = v___y_3064_;
v___y_2513_ = v___y_3065_;
v___y_2514_ = v___y_3066_;
v___y_2515_ = v___y_3067_;
goto v___jp_2506_;
}
}
}
v___jp_3289_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2363_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3291_; lean_object* v_visited_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
lean_dec_ref_known(v___x_3290_, 1);
v___x_3291_ = lean_st_ref_get(v_a_2363_);
v_visited_3292_ = lean_ctor_get(v___x_3291_, 4);
lean_inc(v_visited_3292_);
lean_dec(v___x_3291_);
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_nat_add(v_currRecDepth_3285_, v___x_3293_);
lean_dec(v_currRecDepth_3285_);
v___x_3295_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3295_, 0, v_toCold_3284_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
lean_ctor_set(v___x_3295_, 2, v_ref_3286_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*3, v_diag_3287_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*3 + 1, v_suppressElabErrors_3288_);
v___x_3296_ = lean_unsigned_to_nat(128u);
v___x_3297_ = lean_nat_mod(v_visited_3292_, v___x_3296_);
lean_dec(v_visited_3292_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_nat_dec_eq(v___x_3297_, v___x_3298_);
lean_dec(v___x_3297_);
if (v___x_3299_ == 0)
{
v___y_3061_ = v_a_2362_;
v___y_3062_ = v_a_2363_;
v___y_3063_ = v_a_2364_;
v___y_3064_ = v_a_2365_;
v___y_3065_ = v_a_2366_;
v___y_3066_ = v___x_3295_;
v___y_3067_ = v_a_2368_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3301_ = l_Lean_Core_checkSystem(v___x_3300_, v___x_3295_, v_a_2368_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_dec_ref_known(v___x_3301_, 1);
v___y_3061_ = v_a_2362_;
v___y_3062_ = v_a_2363_;
v___y_3063_ = v_a_2364_;
v___y_3064_ = v_a_2365_;
v___y_3065_ = v_a_2366_;
v___y_3066_ = v___x_3295_;
v___y_3067_ = v_a_2368_;
goto v___jp_3060_;
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref_known(v___x_3295_, 3);
lean_dec_ref(v_code_2361_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_ref_3286_);
lean_dec(v_currRecDepth_3285_);
lean_dec_ref(v_toCold_3284_);
lean_dec_ref(v_code_2361_);
v_a_3310_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3290_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3290_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_params_3332_; lean_object* v_type_3333_; lean_object* v_value_3334_; lean_object* v___x_3335_; lean_object* v_subst_3336_; uint8_t v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_params_3332_ = lean_ctor_get(v_decl_3323_, 2);
v_type_3333_ = lean_ctor_get(v_decl_3323_, 3);
v_value_3334_ = lean_ctor_get(v_decl_3323_, 4);
v___x_3335_ = lean_st_ref_get(v_a_3325_);
v_subst_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_ref(v_subst_3336_);
lean_dec(v___x_3335_);
v___x_3337_ = 0;
v___x_3338_ = 0;
lean_inc_ref(v_type_3333_);
v___x_3339_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3337_, v_subst_3336_, v___x_3338_, v_type_3333_);
lean_dec_ref(v_subst_3336_);
lean_inc_ref(v_params_3332_);
v___x_3340_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3337_, v___x_3338_, v_params_3332_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
lean_inc_ref(v_a_3329_);
lean_inc_ref(v_value_3334_);
v___x_3342_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3334_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3337_, v_decl_3323_, v___x_3339_, v_a_3341_, v_a_3343_, v_a_3328_);
return v___x_3344_;
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3341_);
lean_dec_ref(v___x_3339_);
lean_dec_ref(v_decl_3323_);
v_a_3345_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3342_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3342_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v___x_3339_);
lean_dec_ref(v_decl_3323_);
v_a_3353_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3340_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3340_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3371_, lean_object* v_i_3372_, lean_object* v_as_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3371_, v_i_3372_, v_as_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3393_, lean_object* v_k_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3393_, v_k_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
lean_dec(v_a_3411_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3414_, uint8_t v_t_3415_, lean_object* v_decl_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3414_, v_t_3415_, v_decl_3416_, v___y_3418_, v___y_3421_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3426_, lean_object* v_t_3427_, lean_object* v_decl_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v_pu_boxed_3437_; uint8_t v_t_boxed_3438_; lean_object* v_res_3439_; 
v_pu_boxed_3437_ = lean_unbox(v_pu_3426_);
v_t_boxed_3438_ = lean_unbox(v_t_3427_);
v_res_3439_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3437_, v_t_boxed_3438_, v_decl_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3440_, uint8_t v_t_3441_, lean_object* v_args_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3440_, v_t_3441_, v_args_3442_, v___y_3444_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3452_, lean_object* v_t_3453_, lean_object* v_args_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v_pu_boxed_3463_; uint8_t v_t_boxed_3464_; lean_object* v_res_3465_; 
v_pu_boxed_3463_ = lean_unbox(v_pu_3452_);
v_t_boxed_3464_ = lean_unbox(v_t_3453_);
v_res_3465_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3463_, v_t_boxed_3464_, v_args_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3466_, lean_object* v_R_3467_, lean_object* v_a_3468_, lean_object* v_b_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3468_, v_b_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3471_, lean_object* v_x_3472_, lean_object* v_x_3473_, lean_object* v_x_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3472_, v_x_3473_, v_x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3476_, size_t v_i_3477_, size_t v_stop_3478_, lean_object* v_b_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3476_, v_i_3477_, v_stop_3478_, v_b_3479_, v___y_3481_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3489_, lean_object* v_i_3490_, lean_object* v_stop_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
size_t v_i_boxed_3501_; size_t v_stop_boxed_3502_; lean_object* v_res_3503_; 
v_i_boxed_3501_ = lean_unbox_usize(v_i_3490_);
lean_dec(v_i_3490_);
v_stop_boxed_3502_ = lean_unbox_usize(v_stop_3491_);
lean_dec(v_stop_3491_);
v_res_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3489_, v_i_boxed_3501_, v_stop_boxed_3502_, v_b_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v_as_3489_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3504_, size_t v_i_3505_, size_t v_stop_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3504_, v_i_3505_, v_stop_3506_, v___y_3513_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3516_, lean_object* v_i_3517_, lean_object* v_stop_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
size_t v_i_boxed_3527_; size_t v_stop_boxed_3528_; lean_object* v_res_3529_; 
v_i_boxed_3527_ = lean_unbox_usize(v_i_3517_);
lean_dec(v_i_3517_);
v_stop_boxed_3528_ = lean_unbox_usize(v_stop_3518_);
lean_dec(v_stop_3518_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3516_, v_i_boxed_3527_, v_stop_boxed_3528_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_as_3516_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3530_, size_t v_i_3531_, size_t v_stop_3532_, lean_object* v_b_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3530_, v_i_3531_, v_stop_3532_, v_b_3533_, v___y_3535_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3540_, lean_object* v_i_3541_, lean_object* v_stop_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
size_t v_i_boxed_3549_; size_t v_stop_boxed_3550_; lean_object* v_res_3551_; 
v_i_boxed_3549_ = lean_unbox_usize(v_i_3541_);
lean_dec(v_i_3541_);
v_stop_boxed_3550_ = lean_unbox_usize(v_stop_3542_);
lean_dec(v_stop_3542_);
v_res_3551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3540_, v_i_boxed_3549_, v_stop_boxed_3550_, v_b_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v_as_3540_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3552_, size_t v_i_3553_, size_t v_stop_3554_, lean_object* v_b_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3552_, v_i_3553_, v_stop_3554_, v_b_3555_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3565_, lean_object* v_i_3566_, lean_object* v_stop_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
size_t v_i_boxed_3577_; size_t v_stop_boxed_3578_; lean_object* v_res_3579_; 
v_i_boxed_3577_ = lean_unbox_usize(v_i_3566_);
lean_dec(v_i_3566_);
v_stop_boxed_3578_ = lean_unbox_usize(v_stop_3567_);
lean_dec(v_stop_3567_);
v_res_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3565_, v_i_boxed_3577_, v_stop_boxed_3578_, v_b_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_as_3565_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3580_, size_t v_i_3581_, size_t v_stop_3582_, lean_object* v_b_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3580_, v_i_3581_, v_stop_3582_, v_b_3583_, v___y_3588_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3593_, lean_object* v_i_3594_, lean_object* v_stop_3595_, lean_object* v_b_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
size_t v_i_boxed_3605_; size_t v_stop_boxed_3606_; lean_object* v_res_3607_; 
v_i_boxed_3605_ = lean_unbox_usize(v_i_3594_);
lean_dec(v_i_3594_);
v_stop_boxed_3606_ = lean_unbox_usize(v_stop_3595_);
lean_dec(v_stop_3595_);
v_res_3607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3593_, v_i_boxed_3605_, v_stop_boxed_3606_, v_b_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_as_3593_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3608_, size_t v_i_3609_, size_t v_stop_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3608_, v_i_3609_, v_stop_3610_, v___y_3612_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3620_, lean_object* v_i_3621_, lean_object* v_stop_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
size_t v_i_boxed_3631_; size_t v_stop_boxed_3632_; lean_object* v_res_3633_; 
v_i_boxed_3631_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_stop_boxed_3632_ = lean_unbox_usize(v_stop_3622_);
lean_dec(v_stop_3622_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3620_, v_i_boxed_3631_, v_stop_boxed_3632_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_as_3620_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3634_, size_t v_sz_3635_, size_t v_i_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3634_, v_sz_3635_, v_i_3636_, v_b_3637_, v___y_3639_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3647_, lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
size_t v_sz_boxed_3659_; size_t v_i_boxed_3660_; lean_object* v_res_3661_; 
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3660_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3647_, v_sz_boxed_3659_, v_i_boxed_3660_, v_b_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_as_3647_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3662_, lean_object* v_x_3663_, size_t v_x_3664_, size_t v_x_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3663_, v_x_3664_, v_x_3665_, v_x_3666_, v_x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_, lean_object* v_x_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_){
_start:
{
size_t v_x_47615__boxed_3675_; size_t v_x_47616__boxed_3676_; lean_object* v_res_3677_; 
v_x_47615__boxed_3675_ = lean_unbox_usize(v_x_3671_);
lean_dec(v_x_3671_);
v_x_47616__boxed_3676_ = lean_unbox_usize(v_x_3672_);
lean_dec(v_x_3672_);
v_res_3677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3669_, v_x_3670_, v_x_47615__boxed_3675_, v_x_47616__boxed_3676_, v_x_3673_, v_x_3674_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3678_, uint8_t v_t_3679_, lean_object* v_i_3680_, lean_object* v_as_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3678_, v_t_3679_, v_i_3680_, v_as_3681_, v___y_3683_, v___y_3686_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3691_, lean_object* v_t_3692_, lean_object* v_i_3693_, lean_object* v_as_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_pu_boxed_3703_; uint8_t v_t_boxed_3704_; lean_object* v_res_3705_; 
v_pu_boxed_3703_ = lean_unbox(v_pu_3691_);
v_t_boxed_3704_ = lean_unbox(v_t_3692_);
v_res_3705_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3703_, v_t_boxed_3704_, v_i_3693_, v_as_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3706_, lean_object* v_n_3707_, lean_object* v_k_3708_, lean_object* v_v_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3707_, v_k_3708_, v_v_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3711_, size_t v_depth_3712_, lean_object* v_keys_3713_, lean_object* v_vals_3714_, lean_object* v_heq_3715_, lean_object* v_i_3716_, lean_object* v_entries_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3712_, v_keys_3713_, v_vals_3714_, v_i_3716_, v_entries_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3719_, lean_object* v_depth_3720_, lean_object* v_keys_3721_, lean_object* v_vals_3722_, lean_object* v_heq_3723_, lean_object* v_i_3724_, lean_object* v_entries_3725_){
_start:
{
size_t v_depth_boxed_3726_; lean_object* v_res_3727_; 
v_depth_boxed_3726_ = lean_unbox_usize(v_depth_3720_);
lean_dec(v_depth_3720_);
v_res_3727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3719_, v_depth_boxed_3726_, v_keys_3721_, v_vals_3722_, v_heq_3723_, v_i_3724_, v_entries_3725_);
lean_dec_ref(v_vals_3722_);
lean_dec_ref(v_keys_3721_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3728_, lean_object* v_x_3729_, lean_object* v_x_3730_, lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3729_, v_x_3730_, v_x_3731_, v_x_3732_);
return v___x_3733_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
