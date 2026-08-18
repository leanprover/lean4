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
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
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
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static const lean_array_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* v_m_32_, lean_object* v_query_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_zero_37_; uint8_t v_isZero_38_; 
v_zero_37_ = lean_unsigned_to_nat(0u);
v_isZero_38_ = lean_nat_dec_eq(v_x_35_, v_zero_37_);
if (v_isZero_38_ == 1)
{
lean_dec(v_x_36_);
lean_dec(v_x_35_);
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(2);
return v___x_39_;
}
else
{
lean_object* v_val_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_val_40_ = lean_ctor_get(v_x_34_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v_x_34_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_val_40_);
lean_dec(v_x_34_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_val_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
lean_object* v_keyArray_48_; lean_object* v_valueArray_49_; lean_object* v___x_50_; uint8_t v_isSome_51_; 
v_keyArray_48_ = lean_ctor_get(v_m_32_, 1);
v_valueArray_49_ = lean_ctor_get(v_m_32_, 2);
v___x_50_ = lean_array_fget_borrowed(v_keyArray_48_, v_x_36_);
v_isSome_51_ = lean_noption_is_some(v___x_50_);
if (v_isSome_51_ == 0)
{
lean_dec(v_x_35_);
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_x_36_);
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec(v_x_36_);
v_val_53_ = lean_ctor_get(v_x_34_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v_x_34_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_val_53_);
lean_dec(v_x_34_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_val_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; lean_object* v___y_64_; 
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_35_, v_one_61_);
lean_dec(v_x_35_);
if (v_isSome_51_ == 0)
{
goto v___jp_70_;
}
else
{
lean_object* v___x_72_; uint8_t v_isSome_73_; 
v___x_72_ = lean_array_fget_borrowed(v_valueArray_49_, v_x_36_);
v_isSome_73_ = lean_noption_is_some(v___x_72_);
if (v_isSome_73_ == 0)
{
goto v___jp_70_;
}
else
{
lean_object* v_val_74_; uint8_t v___x_75_; 
lean_inc(v___x_50_);
v_val_74_ = lean_noption_get(v___x_50_);
v___x_75_ = l_Lean_instBEqFVarId_beq(v_val_74_, v_query_33_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
lean_dec(v_val_74_);
v___x_76_ = lean_array_get_size(v_keyArray_48_);
v___x_77_ = lean_nat_add(v_x_36_, v_one_61_);
lean_dec(v_x_36_);
v___x_78_ = lean_nat_dec_lt(v___x_77_, v___x_76_);
if (v___x_78_ == 0)
{
lean_dec(v___x_77_);
v_x_35_ = v_n_62_;
v_x_36_ = v_zero_37_;
goto _start;
}
else
{
v_x_35_ = v_n_62_;
v_x_36_ = v___x_77_;
goto _start;
}
}
else
{
lean_object* v_val_81_; lean_object* v___x_82_; 
lean_dec(v_n_62_);
lean_dec(v_x_34_);
lean_inc(v___x_72_);
v_val_81_ = lean_noption_get(v___x_72_);
v___x_82_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_82_, 0, v_x_36_);
lean_ctor_set(v___x_82_, 1, v_val_74_);
lean_ctor_set(v___x_82_, 2, v_val_81_);
return v___x_82_;
}
}
}
v___jp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_array_get_size(v_keyArray_48_);
v___x_66_ = lean_nat_add(v_x_36_, v_one_61_);
lean_dec(v_x_36_);
v___x_67_ = lean_nat_dec_lt(v___x_66_, v___x_65_);
if (v___x_67_ == 0)
{
lean_dec(v___x_66_);
v_x_34_ = v___y_64_;
v_x_35_ = v_n_62_;
v_x_36_ = v_zero_37_;
goto _start;
}
else
{
v_x_34_ = v___y_64_;
v_x_35_ = v_n_62_;
v_x_36_ = v___x_66_;
goto _start;
}
}
v___jp_70_:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_71_; 
lean_inc(v_x_36_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v_x_36_);
v___y_64_ = v___x_71_;
goto v___jp_63_;
}
else
{
v___y_64_ = v_x_34_;
goto v___jp_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* v_m_83_, lean_object* v_query_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_m_83_, v_query_84_, v_x_85_, v_x_86_, v_x_87_);
lean_dec(v_query_84_);
lean_dec_ref(v_m_83_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* v_m_89_, lean_object* v_query_90_){
_start:
{
lean_object* v_keyArray_91_; lean_object* v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; uint64_t v_fold_96_; uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_keyArray_91_ = lean_ctor_get(v_m_89_, 1);
v___x_92_ = lean_array_get_size(v_keyArray_91_);
v___x_93_ = l_Lean_instHashableFVarId_hash(v_query_90_);
v___x_94_ = 32ULL;
v___x_95_ = lean_uint64_shift_right(v___x_93_, v___x_94_);
v_fold_96_ = lean_uint64_xor(v___x_93_, v___x_95_);
v___x_97_ = 16ULL;
v___x_98_ = lean_uint64_shift_right(v_fold_96_, v___x_97_);
v___x_99_ = lean_uint64_xor(v_fold_96_, v___x_98_);
v___x_100_ = lean_uint64_to_usize(v___x_99_);
v___x_101_ = lean_usize_of_nat(v___x_92_);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_sub(v___x_101_, v___x_102_);
v___x_104_ = lean_usize_land(v___x_100_, v___x_103_);
v___x_105_ = lean_usize_to_nat(v___x_104_);
v___x_106_ = lean_box(0);
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_m_89_, v_query_90_, v___x_106_, v___x_92_, v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object* v_m_108_, lean_object* v_query_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_108_, v_query_109_);
lean_dec(v_query_109_);
lean_dec_ref(v_m_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg(lean_object* v_b_111_, lean_object* v_acc_112_, lean_object* v_i_113_){
_start:
{
lean_object* v___y_115_; lean_object* v_keyArray_123_; lean_object* v_valueArray_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_keyArray_123_ = lean_ctor_get(v_b_111_, 1);
v_valueArray_124_ = lean_ctor_get(v_b_111_, 2);
v___x_125_ = lean_array_get_size(v_keyArray_123_);
v___x_126_ = lean_nat_dec_lt(v_i_113_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_i_113_);
return v_acc_112_;
}
else
{
lean_object* v___x_127_; uint8_t v_isSome_128_; 
v___x_127_ = lean_array_fget_borrowed(v_keyArray_123_, v_i_113_);
v_isSome_128_ = lean_noption_is_some(v___x_127_);
if (v_isSome_128_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v___x_129_; uint8_t v_isSome_130_; 
v___x_129_ = lean_array_fget_borrowed(v_valueArray_124_, v_i_113_);
v_isSome_130_ = lean_noption_is_some(v___x_129_);
if (v_isSome_130_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v_val_131_; lean_object* v_val_132_; lean_object* v_i_134_; lean_object* v___x_139_; 
lean_inc(v___x_127_);
v_val_131_ = lean_noption_get(v___x_127_);
lean_inc(v___x_129_);
v_val_132_ = lean_noption_get(v___x_129_);
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_acc_112_, v_val_131_);
switch(lean_obj_tag(v___x_139_))
{
case 0:
{
lean_object* v_index_140_; lean_object* v_size_141_; lean_object* v___x_142_; 
v_index_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_index_140_);
lean_dec_ref_known(v___x_139_, 3);
v_size_141_ = lean_ctor_get(v_acc_112_, 0);
lean_inc(v_size_141_);
v___x_142_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_112_, v_size_141_, v_index_140_, v_val_131_, v_val_132_);
lean_dec(v_index_140_);
v___y_115_ = v___x_142_;
goto v___jp_114_;
}
case 1:
{
lean_object* v_index_143_; 
v_index_143_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_139_, 1);
v_i_134_ = v_index_143_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_112_, v___x_144_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_145_, 1);
v_i_134_ = v_index_146_;
goto v___jp_133_;
}
else
{
lean_dec(v_val_132_);
lean_dec(v_val_131_);
v___y_115_ = v_acc_112_;
goto v___jp_114_;
}
}
}
v___jp_133_:
{
lean_object* v_size_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_size_135_ = lean_ctor_get(v_acc_112_, 0);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_size_135_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_112_, v___x_137_, v_i_134_, v_val_131_, v_val_132_);
lean_dec(v_i_134_);
v___y_115_ = v___x_138_;
goto v___jp_114_;
}
}
}
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_i_113_, v___x_116_);
lean_dec(v_i_113_);
v_acc_112_ = v___y_115_;
v_i_113_ = v___x_117_;
goto _start;
}
v___jp_119_:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_i_113_, v___x_120_);
lean_dec(v_i_113_);
v_i_113_ = v___x_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_147_, lean_object* v_acc_148_, lean_object* v_i_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg(v_b_147_, v_acc_148_, v_i_149_);
lean_dec_ref(v_b_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg(lean_object* v_init_151_, lean_object* v_b_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg(v_b_152_, v_init_151_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg___boxed(lean_object* v_init_155_, lean_object* v_b_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg(v_init_155_, v_b_156_);
lean_dec_ref(v_b_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* v_m_158_){
_start:
{
lean_object* v_keyArray_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_cellCount_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_target_166_; lean_object* v___x_167_; 
v_keyArray_159_ = lean_ctor_get(v_m_158_, 1);
v___x_160_ = lean_array_get_size(v_keyArray_159_);
v___x_161_ = lean_unsigned_to_nat(2u);
v_cellCount_162_ = lean_nat_mul(v___x_160_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_162_);
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_162_);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_162_);
v_target_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_166_, 0, v___x_163_);
lean_ctor_set(v_target_166_, 1, v___x_164_);
lean_ctor_set(v_target_166_, 2, v___x_165_);
v___x_167_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg(v_target_166_, v_m_158_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* v_m_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_m_168_);
lean_dec_ref(v_m_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* v_as_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_b_173_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_lt(v_i_172_, v_sz_171_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v_b_173_);
return v___x_176_;
}
else
{
lean_object* v_snd_177_; lean_object* v_fst_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_273_; 
v_snd_177_ = lean_ctor_get(v_b_173_, 1);
v_fst_178_ = lean_ctor_get(v_b_173_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_b_173_);
if (v_isSharedCheck_273_ == 0)
{
v___x_180_ = v_b_173_;
v_isShared_181_ = v_isSharedCheck_273_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snd_177_);
lean_inc(v_fst_178_);
lean_dec(v_b_173_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_273_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_array_182_; lean_object* v_start_183_; lean_object* v_stop_184_; uint8_t v___x_185_; 
v_array_182_ = lean_ctor_get(v_snd_177_, 0);
v_start_183_ = lean_ctor_get(v_snd_177_, 1);
v_stop_184_ = lean_ctor_get(v_snd_177_, 2);
v___x_185_ = lean_nat_dec_lt(v_start_183_, v_stop_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_187_; 
if (v_isShared_181_ == 0)
{
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_fst_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_snd_177_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
else
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_269_; 
lean_inc(v_stop_184_);
lean_inc(v_start_183_);
lean_inc_ref(v_array_182_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_snd_177_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_270_ = lean_ctor_get(v_snd_177_, 2);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_snd_177_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_snd_177_, 0);
lean_dec(v_unused_272_);
v___x_191_ = v_snd_177_;
v_isShared_192_ = v_isSharedCheck_269_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_snd_177_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_269_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_a_193_; lean_object* v_fvarId_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v_a_193_ = lean_array_uget_borrowed(v_as_170_, v_i_172_);
v_fvarId_194_ = lean_ctor_get(v_a_193_, 0);
v___x_195_ = lean_array_fget(v_array_182_, v_start_183_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_start_183_, v___x_196_);
lean_dec(v_start_183_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_197_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_array_182_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_stop_184_);
v___x_199_ = v_reuseFailAlloc_268_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___y_201_; lean_object* v___y_209_; lean_object* v_i_210_; lean_object* v___y_225_; lean_object* v_i_226_; lean_object* v___y_231_; lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_178_, v_fvarId_194_);
switch(lean_obj_tag(v___x_240_))
{
case 0:
{
lean_object* v_index_241_; lean_object* v_size_242_; lean_object* v___x_243_; 
v_index_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_index_241_);
lean_dec_ref_known(v___x_240_, 3);
v_size_242_ = lean_ctor_get(v_fst_178_, 0);
lean_inc(v_size_242_);
lean_inc(v_fvarId_194_);
v___x_243_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_178_, v_size_242_, v_index_241_, v_fvarId_194_, v___x_195_);
lean_dec(v_index_241_);
v___y_201_ = v___x_243_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_244_; lean_object* v_size_245_; lean_object* v_keyArray_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_index_244_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_index_244_);
lean_dec_ref_known(v___x_240_, 1);
v_size_245_ = lean_ctor_get(v_fst_178_, 0);
v_keyArray_246_ = lean_ctor_get(v_fst_178_, 1);
v___x_247_ = lean_nat_add(v_size_245_, v___x_196_);
v___x_248_ = lean_array_get_size(v_keyArray_246_);
v___x_249_ = lean_nat_dec_lt(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec(v___x_247_);
lean_dec(v_index_244_);
goto v___jp_214_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_250_ = lean_unsigned_to_nat(4u);
v___x_251_ = lean_nat_mul(v___x_247_, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(3u);
v___x_253_ = lean_nat_mul(v___x_248_, v___x_252_);
v___x_254_ = lean_nat_dec_le(v___x_251_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_251_);
if (v___x_254_ == 0)
{
lean_dec(v___x_247_);
lean_dec(v_index_244_);
goto v___jp_214_;
}
else
{
lean_object* v___x_255_; 
lean_inc(v_fvarId_194_);
v___x_255_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_178_, v___x_247_, v_index_244_, v_fvarId_194_, v___x_195_);
lean_dec(v_index_244_);
v___y_201_ = v___x_255_;
goto v___jp_200_;
}
}
}
default: 
{
lean_object* v_size_256_; lean_object* v_keyArray_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_size_256_ = lean_ctor_get(v_fst_178_, 0);
v_keyArray_257_ = lean_ctor_get(v_fst_178_, 1);
v___x_258_ = lean_nat_add(v_size_256_, v___x_196_);
v___x_259_ = lean_array_get_size(v_keyArray_257_);
v___x_260_ = lean_nat_dec_lt(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v___x_258_);
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_178_);
lean_dec(v_fst_178_);
v___y_231_ = v___x_261_;
goto v___jp_230_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_262_ = lean_unsigned_to_nat(4u);
v___x_263_ = lean_nat_mul(v___x_258_, v___x_262_);
lean_dec(v___x_258_);
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = lean_nat_mul(v___x_259_, v___x_264_);
v___x_266_ = lean_nat_dec_le(v___x_263_, v___x_265_);
lean_dec(v___x_265_);
lean_dec(v___x_263_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_178_);
lean_dec(v_fst_178_);
v___y_231_ = v___x_267_;
goto v___jp_230_;
}
else
{
v___y_231_ = v_fst_178_;
goto v___jp_230_;
}
}
}
}
v___jp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_199_);
lean_ctor_set(v___x_180_, 0, v___y_201_);
v___x_203_ = v___x_180_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___y_201_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_199_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
size_t v___x_204_; size_t v___x_205_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_add(v_i_172_, v___x_204_);
v_i_172_ = v___x_205_;
v_b_173_ = v___x_203_;
goto _start;
}
}
v___jp_208_:
{
lean_object* v_size_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_size_211_ = lean_ctor_get(v___y_209_, 0);
v___x_212_ = lean_nat_add(v_size_211_, v___x_196_);
lean_inc(v_fvarId_194_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_209_, v___x_212_, v_i_210_, v_fvarId_194_, v___x_195_);
lean_dec(v_i_210_);
v___y_201_ = v___x_213_;
goto v___jp_200_;
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_178_);
lean_dec(v_fst_178_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___x_215_, v_fvarId_194_);
switch(lean_obj_tag(v___x_216_))
{
case 0:
{
lean_object* v_index_217_; lean_object* v_size_218_; lean_object* v___x_219_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 3);
v_size_218_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_size_218_);
lean_inc(v_fvarId_194_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_215_, v_size_218_, v_index_217_, v_fvarId_194_, v___x_195_);
lean_dec(v_index_217_);
v___y_201_ = v___x_219_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_220_; 
v_index_220_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_216_, 1);
v___y_209_ = v___x_215_;
v_i_210_ = v_index_220_;
goto v___jp_208_;
}
default: 
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_215_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_index_223_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_209_ = v___x_215_;
v_i_210_ = v_index_223_;
goto v___jp_208_;
}
else
{
lean_dec(v___x_195_);
v___y_201_ = v___x_215_;
goto v___jp_200_;
}
}
}
}
v___jp_224_:
{
lean_object* v_size_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_size_227_ = lean_ctor_get(v___y_225_, 0);
v___x_228_ = lean_nat_add(v_size_227_, v___x_196_);
lean_inc(v_fvarId_194_);
v___x_229_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_225_, v___x_228_, v_i_226_, v_fvarId_194_, v___x_195_);
lean_dec(v_i_226_);
v___y_201_ = v___x_229_;
goto v___jp_200_;
}
v___jp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___y_231_, v_fvarId_194_);
switch(lean_obj_tag(v___x_232_))
{
case 0:
{
lean_object* v_index_233_; lean_object* v_size_234_; lean_object* v___x_235_; 
v_index_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_233_);
lean_dec_ref_known(v___x_232_, 3);
v_size_234_ = lean_ctor_get(v___y_231_, 0);
lean_inc(v_size_234_);
lean_inc(v_fvarId_194_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_231_, v_size_234_, v_index_233_, v_fvarId_194_, v___x_195_);
lean_dec(v_index_233_);
v___y_201_ = v___x_235_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_236_; 
v_index_236_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_236_);
lean_dec_ref_known(v___x_232_, 1);
v___y_225_ = v___y_231_;
v_i_226_ = v_index_236_;
goto v___jp_224_;
}
default: 
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_231_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_index_239_; 
v_index_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_238_, 1);
v___y_225_ = v___y_231_;
v_i_226_ = v_index_239_;
goto v___jp_224_;
}
else
{
lean_dec(v___x_195_);
v___y_201_ = v___y_231_;
goto v___jp_200_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* v_as_274_, lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_b_277_, lean_object* v___y_278_){
_start:
{
size_t v_sz_boxed_279_; size_t v_i_boxed_280_; lean_object* v_res_281_; 
v_sz_boxed_279_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_280_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_as_274_, v_sz_boxed_279_, v_i_boxed_280_, v_b_277_);
lean_dec_ref(v_as_274_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg(lean_object* v_a_282_, lean_object* v_b_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_array_289_; lean_object* v_start_290_; lean_object* v_stop_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_402_; 
v_array_289_ = lean_ctor_get(v_a_282_, 0);
v_start_290_ = lean_ctor_get(v_a_282_, 1);
v_stop_291_ = lean_ctor_get(v_a_282_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_402_ == 0)
{
v___x_293_ = v_a_282_;
v_isShared_294_ = v_isSharedCheck_402_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_stop_291_);
lean_inc(v_start_290_);
lean_inc(v_array_289_);
lean_dec(v_a_282_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_402_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_lt(v_start_290_, v_stop_291_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_del_object(v___x_293_);
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
lean_dec_ref(v_array_289_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_b_283_);
return v___x_296_;
}
else
{
lean_object* v_fst_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_401_; 
v_fst_297_ = lean_ctor_get(v_b_283_, 0);
v_snd_298_ = lean_ctor_get(v_b_283_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_b_283_);
if (v_isSharedCheck_401_ == 0)
{
v___x_300_ = v_b_283_;
v_isShared_301_ = v_isSharedCheck_401_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_297_);
lean_dec(v_b_283_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_401_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_fvarId_303_; lean_object* v_type_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_302_ = lean_array_fget_borrowed(v_array_289_, v_start_290_);
v_fvarId_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_fvarId_303_);
v_type_304_ = lean_ctor_get(v___x_302_, 2);
v___x_305_ = 0;
lean_inc_ref(v_type_304_);
v___x_306_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v___x_305_, v_type_304_, v_fst_297_, v___x_295_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; uint8_t v___x_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = 0;
v___x_309_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_305_, v_a_307_, v___x_308_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_fvarId_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_fvarId_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_fvarId_311_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_start_290_, v___x_312_);
lean_dec(v_start_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_313_);
v___x_315_ = v___x_293_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_array_289_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_stop_291_);
v___x_315_ = v_reuseFailAlloc_384_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___y_318_; lean_object* v___x_323_; lean_object* v___y_325_; lean_object* v_i_326_; lean_object* v___y_331_; lean_object* v___y_341_; lean_object* v_i_342_; lean_object* v___x_356_; 
v___x_316_ = lean_array_push(v_snd_298_, v_a_310_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_fvarId_311_);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_297_, v_fvarId_303_);
switch(lean_obj_tag(v___x_356_))
{
case 0:
{
lean_object* v_index_357_; lean_object* v_size_358_; lean_object* v___x_359_; 
v_index_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_index_357_);
lean_dec_ref_known(v___x_356_, 3);
v_size_358_ = lean_ctor_get(v_fst_297_, 0);
lean_inc(v_size_358_);
v___x_359_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_297_, v_size_358_, v_index_357_, v_fvarId_303_, v___x_323_);
lean_dec(v_index_357_);
v___y_318_ = v___x_359_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_360_; lean_object* v_size_361_; lean_object* v_keyArray_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_index_360_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_index_360_);
lean_dec_ref_known(v___x_356_, 1);
v_size_361_ = lean_ctor_get(v_fst_297_, 0);
v_keyArray_362_ = lean_ctor_get(v_fst_297_, 1);
v___x_363_ = lean_nat_add(v_size_361_, v___x_312_);
v___x_364_ = lean_array_get_size(v_keyArray_362_);
v___x_365_ = lean_nat_dec_lt(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_dec(v___x_363_);
lean_dec(v_index_360_);
goto v___jp_346_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(4u);
v___x_367_ = lean_nat_mul(v___x_363_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = lean_nat_mul(v___x_364_, v___x_368_);
v___x_370_ = lean_nat_dec_le(v___x_367_, v___x_369_);
lean_dec(v___x_369_);
lean_dec(v___x_367_);
if (v___x_370_ == 0)
{
lean_dec(v___x_363_);
lean_dec(v_index_360_);
goto v___jp_346_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_297_, v___x_363_, v_index_360_, v_fvarId_303_, v___x_323_);
lean_dec(v_index_360_);
v___y_318_ = v___x_371_;
goto v___jp_317_;
}
}
}
default: 
{
lean_object* v_size_372_; lean_object* v_keyArray_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_size_372_ = lean_ctor_get(v_fst_297_, 0);
v_keyArray_373_ = lean_ctor_get(v_fst_297_, 1);
v___x_374_ = lean_nat_add(v_size_372_, v___x_312_);
v___x_375_ = lean_array_get_size(v_keyArray_373_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v___x_374_);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_297_);
lean_dec(v_fst_297_);
v___y_331_ = v___x_377_;
goto v___jp_330_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_nat_mul(v___x_374_, v___x_378_);
lean_dec(v___x_374_);
v___x_380_ = lean_unsigned_to_nat(3u);
v___x_381_ = lean_nat_mul(v___x_375_, v___x_380_);
v___x_382_ = lean_nat_dec_le(v___x_379_, v___x_381_);
lean_dec(v___x_381_);
lean_dec(v___x_379_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_297_);
lean_dec(v_fst_297_);
v___y_331_ = v___x_383_;
goto v___jp_330_;
}
else
{
v___y_331_ = v_fst_297_;
goto v___jp_330_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_316_);
lean_ctor_set(v___x_300_, 0, v___y_318_);
v___x_320_ = v___x_300_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___y_318_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_316_);
v___x_320_ = v_reuseFailAlloc_322_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v_a_282_ = v___x_315_;
v_b_283_ = v___x_320_;
goto _start;
}
}
v___jp_324_:
{
lean_object* v_size_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_size_327_ = lean_ctor_get(v___y_325_, 0);
v___x_328_ = lean_nat_add(v_size_327_, v___x_312_);
v___x_329_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_325_, v___x_328_, v_i_326_, v_fvarId_303_, v___x_323_);
lean_dec(v_i_326_);
v___y_318_ = v___x_329_;
goto v___jp_317_;
}
v___jp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___y_331_, v_fvarId_303_);
switch(lean_obj_tag(v___x_332_))
{
case 0:
{
lean_object* v_index_333_; lean_object* v_size_334_; lean_object* v___x_335_; 
v_index_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_index_333_);
lean_dec_ref_known(v___x_332_, 3);
v_size_334_ = lean_ctor_get(v___y_331_, 0);
lean_inc(v_size_334_);
v___x_335_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_331_, v_size_334_, v_index_333_, v_fvarId_303_, v___x_323_);
lean_dec(v_index_333_);
v___y_318_ = v___x_335_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_336_; 
v_index_336_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_index_336_);
lean_dec_ref_known(v___x_332_, 1);
v___y_325_ = v___y_331_;
v_i_326_ = v_index_336_;
goto v___jp_324_;
}
default: 
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_331_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_index_339_; 
v_index_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_index_339_);
lean_dec_ref_known(v___x_338_, 1);
v___y_325_ = v___y_331_;
v_i_326_ = v_index_339_;
goto v___jp_324_;
}
else
{
lean_dec_ref_known(v___x_323_, 1);
lean_dec(v_fvarId_303_);
v___y_318_ = v___y_331_;
goto v___jp_317_;
}
}
}
}
v___jp_340_:
{
lean_object* v_size_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_size_343_ = lean_ctor_get(v___y_341_, 0);
v___x_344_ = lean_nat_add(v_size_343_, v___x_312_);
v___x_345_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_341_, v___x_344_, v_i_342_, v_fvarId_303_, v___x_323_);
lean_dec(v_i_342_);
v___y_318_ = v___x_345_;
goto v___jp_317_;
}
v___jp_346_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_fst_297_);
lean_dec(v_fst_297_);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___x_347_, v_fvarId_303_);
switch(lean_obj_tag(v___x_348_))
{
case 0:
{
lean_object* v_index_349_; lean_object* v_size_350_; lean_object* v___x_351_; 
v_index_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_index_349_);
lean_dec_ref_known(v___x_348_, 3);
v_size_350_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_size_350_);
v___x_351_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_347_, v_size_350_, v_index_349_, v_fvarId_303_, v___x_323_);
lean_dec(v_index_349_);
v___y_318_ = v___x_351_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_352_; 
v_index_352_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_index_352_);
lean_dec_ref_known(v___x_348_, 1);
v___y_341_ = v___x_347_;
v_i_342_ = v_index_352_;
goto v___jp_340_;
}
default: 
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_347_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_index_355_; 
v_index_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_index_355_);
lean_dec_ref_known(v___x_354_, 1);
v___y_341_ = v___x_347_;
v_i_342_ = v_index_355_;
goto v___jp_340_;
}
else
{
lean_dec_ref_known(v___x_323_, 1);
lean_dec(v_fvarId_303_);
v___y_318_ = v___x_347_;
goto v___jp_317_;
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_fvarId_303_);
lean_del_object(v___x_300_);
lean_dec(v_snd_298_);
lean_dec(v_fst_297_);
lean_del_object(v___x_293_);
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
lean_dec_ref(v_array_289_);
v_a_385_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_309_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_309_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_fvarId_303_);
lean_del_object(v___x_300_);
lean_dec(v_snd_298_);
lean_dec(v_fst_297_);
lean_del_object(v___x_293_);
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
lean_dec_ref(v_array_289_);
v_a_393_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_306_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_306_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg___boxed(lean_object* v_a_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg(v_a_403_, v_b_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0(void){
_start:
{
lean_object* v_cellCount_411_; lean_object* v___x_412_; 
v_cellCount_411_ = lean_unsigned_to_nat(16u);
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1(void){
_start:
{
lean_object* v_cellCount_413_; lean_object* v___x_414_; 
v_cellCount_413_ = lean_unsigned_to_nat(16u);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_subst_418_; 
v___x_415_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
v___x_416_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
v___x_417_ = lean_unsigned_to_nat(0u);
v_subst_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_subst_418_, 0, v___x_417_);
lean_ctor_set(v_subst_418_, 1, v___x_416_);
lean_ctor_set(v_subst_418_, 2, v___x_415_);
return v_subst_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* v_info_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_params_433_; lean_object* v_value_434_; lean_object* v_args_435_; lean_object* v___x_436_; lean_object* v_subst_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; 
v_params_433_ = lean_ctor_get(v_info_424_, 0);
lean_inc_ref(v_params_433_);
v_value_434_ = lean_ctor_get(v_info_424_, 1);
lean_inc_ref(v_value_434_);
v_args_435_ = lean_ctor_get(v_info_424_, 3);
lean_inc_ref(v_args_435_);
lean_dec_ref(v_info_424_);
v___x_436_ = lean_unsigned_to_nat(0u);
v_subst_437_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2);
v___x_438_ = lean_array_get_size(v_args_435_);
v___x_439_ = l_Array_toSubarray___redArg(v_args_435_, v___x_436_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_subst_437_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v_sz_441_ = lean_array_size(v_params_433_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_params_433_, v_sz_441_, v___x_442_, v___x_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_fst_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_494_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v_fst_445_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_a_444_, 1);
lean_dec(v_unused_495_);
v___x_447_ = v_a_444_;
v_isShared_448_ = v_isSharedCheck_494_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_fst_445_);
lean_dec(v_a_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_494_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v_lower_451_; lean_object* v_upper_452_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_449_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3));
v___x_492_ = lean_array_get_size(v_params_433_);
v___x_493_ = lean_nat_dec_le(v___x_438_, v___x_436_);
if (v___x_493_ == 0)
{
v_lower_451_ = v___x_438_;
v_upper_452_ = v___x_492_;
goto v___jp_450_;
}
else
{
v_lower_451_ = v___x_436_;
v_upper_452_ = v___x_492_;
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_Array_toSubarray___redArg(v_params_433_, v_lower_451_, v_upper_452_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_449_);
v___x_455_ = v___x_447_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_fst_445_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_449_);
v___x_455_ = v_reuseFailAlloc_491_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg(v___x_453_, v___x_455_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_fst_458_; lean_object* v_snd_459_; uint8_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v_fst_458_ = lean_ctor_get(v_a_457_, 0);
lean_inc(v_fst_458_);
v_snd_459_ = lean_ctor_get(v_a_457_, 1);
lean_inc(v_snd_459_);
lean_dec(v_a_457_);
v___x_460_ = 0;
v___x_461_ = 0;
v___x_462_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_460_, v_value_434_, v_fst_458_, v___x_461_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc_n(v_a_463_, 2);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_463_, v___x_461_, v_a_426_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref_known(v___x_464_, 1);
v___x_465_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5));
v___x_466_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_snd_459_, v_a_463_, v___x_465_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_466_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_a_463_);
lean_dec(v_snd_459_);
v_a_467_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_464_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_464_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_snd_459_);
v_a_475_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_462_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_462_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v_value_434_);
v_a_483_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_456_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_456_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_value_434_);
lean_dec_ref(v_params_433_);
v_a_496_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_443_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_443_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* v_info_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_info_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_query_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_515_, v_query_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_query_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(v_00_u03b2_518_, v_m_519_, v_query_520_);
lean_dec(v_query_520_);
lean_dec_ref(v_m_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_m_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_m_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* v_00_u03b2_525_, lean_object* v_m_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_00_u03b2_525_, v_m_526_);
lean_dec_ref(v_m_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* v_as_528_, size_t v_sz_529_, size_t v_i_530_, lean_object* v_b_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_as_528_, v_sz_529_, v_i_530_, v_b_531_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* v_as_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_554_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(v_as_541_, v_sz_boxed_553_, v_i_boxed_554_, v_b_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec_ref(v_as_541_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3(lean_object* v_inst_556_, lean_object* v_R_557_, lean_object* v_a_558_, lean_object* v_b_559_, lean_object* v_c_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___redArg(v_a_558_, v_b_559_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3___boxed(lean_object* v_inst_570_, lean_object* v_R_571_, lean_object* v_a_572_, lean_object* v_b_573_, lean_object* v_c_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__3(v_inst_570_, v_R_571_, v_a_572_, v_b_573_, v_c_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* v_00_u03b2_584_, lean_object* v_m_585_, lean_object* v_query_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_m_585_, v_query_586_, v_x_587_, v_x_588_, v_x_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* v_00_u03b2_592_, lean_object* v_m_593_, lean_object* v_query_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_592_, v_m_593_, v_query_594_, v_x_595_, v_x_596_, v_x_597_, v_x_598_);
lean_dec(v_query_594_);
lean_dec_ref(v_m_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2(lean_object* v_00_u03b2_600_, lean_object* v_init_601_, lean_object* v_b_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___redArg(v_init_601_, v_b_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2___boxed(lean_object* v_00_u03b2_604_, lean_object* v_init_605_, lean_object* v_b_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2(v_00_u03b2_604_, v_init_605_, v_b_606_);
lean_dec_ref(v_b_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_608_, lean_object* v_b_609_, lean_object* v_acc_610_, lean_object* v_i_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___redArg(v_b_609_, v_acc_610_, v_i_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_613_, lean_object* v_b_614_, lean_object* v_acc_615_, lean_object* v_i_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_spec__2_spec__3(v_00_u03b2_613_, v_b_614_, v_acc_615_, v_i_616_);
lean_dec_ref(v_b_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* v_fvarId_618_, lean_object* v_args_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
uint8_t v___x_628_; lean_object* v___x_629_; 
v___x_628_ = 0;
v___x_629_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_628_, v_fvarId_618_, v_a_624_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_694_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_694_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_694_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_694_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
if (lean_obj_tag(v_a_630_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_632_);
v_val_634_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_689_ == 0)
{
v___x_636_ = v_a_630_;
v_isShared_637_ = v_isSharedCheck_689_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v_a_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_689_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_val_634_, v_a_621_, v_a_623_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_680_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_680_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_680_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_680_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_unbox(v_a_639_);
lean_dec(v_a_639_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_del_object(v___x_636_);
lean_dec(v_val_634_);
lean_dec_ref(v_args_619_);
v___x_644_ = lean_box(0);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v___x_648_; 
lean_del_object(v___x_641_);
v___x_648_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_621_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_params_649_; lean_object* v_value_650_; uint8_t v___x_651_; lean_object* v___x_652_; 
lean_dec_ref_known(v___x_648_, 1);
v_params_649_ = lean_ctor_get(v_val_634_, 2);
lean_inc_ref(v_params_649_);
v_value_650_ = lean_ctor_get(v_val_634_, 4);
lean_inc_ref(v_value_650_);
lean_dec(v_val_634_);
v___x_651_ = 0;
v___x_652_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_649_, v_value_650_, v_args_619_, v___x_651_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec_ref(v_params_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_663_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_663_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_a_653_);
v___x_658_ = v___x_636_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_del_object(v___x_636_);
v_a_664_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_652_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_652_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_636_);
lean_dec(v_val_634_);
lean_dec_ref(v_args_619_);
v_a_672_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_648_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_648_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_del_object(v___x_636_);
lean_dec(v_val_634_);
lean_dec_ref(v_args_619_);
v_a_681_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_638_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_638_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_692_; 
lean_dec(v_a_630_);
lean_dec_ref(v_args_619_);
v___x_690_ = lean_box(0);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_690_);
v___x_692_ = v___x_632_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v_args_619_);
v_a_695_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_629_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_629_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* v_fvarId_703_, lean_object* v_args_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_703_, v_args_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_fvarId_703_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* v_declName_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v_env_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_717_ = lean_st_ref_get(v___y_715_);
v_env_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_ref(v_env_718_);
lean_dec(v___x_717_);
v___x_719_ = l_Lean_isInstanceReducibleCore(v_env_718_, v_declName_714_);
v___x_720_ = lean_box(v___x_719_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_723_, v___y_724_);
lean_dec(v___y_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* v_declName_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_727_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* v_declName_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t v_sz_747_, size_t v_i_748_, lean_object* v_bs_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_lt(v_i_748_, v_sz_747_);
if (v___x_750_ == 0)
{
return v_bs_749_;
}
else
{
lean_object* v_v_751_; lean_object* v_fvarId_752_; lean_object* v___x_753_; lean_object* v_bs_x27_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_v_751_ = lean_array_uget_borrowed(v_bs_749_, v_i_748_);
v_fvarId_752_ = lean_ctor_get(v_v_751_, 0);
lean_inc(v_fvarId_752_);
v___x_753_ = lean_unsigned_to_nat(0u);
v_bs_x27_754_ = lean_array_uset(v_bs_749_, v_i_748_, v___x_753_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_fvarId_752_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_748_, v___x_756_);
v___x_758_ = lean_array_uset(v_bs_x27_754_, v_i_748_, v___x_755_);
v_i_748_ = v___x_757_;
v_bs_749_ = v___x_758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* v_letDecl_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_config_778_; uint8_t v_etaPoly_779_; 
v_config_778_ = lean_ctor_get(v_a_770_, 1);
v_etaPoly_779_ = lean_ctor_get_uint8(v_config_778_, 0);
if (v_etaPoly_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_letDecl_769_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
else
{
lean_object* v_value_782_; 
v_value_782_ = lean_ctor_get(v_letDecl_769_, 3);
lean_inc(v_value_782_);
if (lean_obj_tag(v_value_782_) == 3)
{
lean_object* v_fvarId_783_; lean_object* v_type_784_; lean_object* v_declName_785_; lean_object* v_us_786_; lean_object* v_args_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_956_; 
v_fvarId_783_ = lean_ctor_get(v_letDecl_769_, 0);
v_type_784_ = lean_ctor_get(v_letDecl_769_, 2);
v_declName_785_ = lean_ctor_get(v_value_782_, 0);
v_us_786_ = lean_ctor_get(v_value_782_, 1);
v_args_787_ = lean_ctor_get(v_value_782_, 2);
v_isSharedCheck_956_ = !lean_is_exclusive(v_value_782_);
if (v_isSharedCheck_956_ == 0)
{
v___x_789_ = v_value_782_;
v_isShared_790_ = v_isSharedCheck_956_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_args_787_);
lean_inc(v_us_786_);
lean_inc(v_declName_785_);
lean_dec(v_value_782_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_956_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v_env_792_; uint8_t v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_st_ref_get(v_a_776_);
v_env_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_env_792_);
lean_dec(v___x_791_);
v___x_793_ = 0;
lean_inc(v_declName_785_);
v___x_794_ = l_Lean_Environment_find_x3f(v_env_792_, v_declName_785_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 1)
{
lean_object* v_val_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_val_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = l_Lean_ConstantInfo_type(v_val_795_);
lean_dec(v_val_795_);
v___x_797_ = l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_796_, v_a_776_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_945_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_945_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_945_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_945_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v___x_803_ = lean_box(0);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_944_; 
lean_del_object(v___x_800_);
lean_inc(v_declName_785_);
v___x_807_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_785_, v_a_776_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_944_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_944_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_944_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_943_; 
v_val_812_ = lean_ctor_get(v_a_808_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_943_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_943_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_943_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = lean_unbox(v_val_812_);
lean_dec(v_val_812_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_del_object(v___x_810_);
v___x_817_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_773_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_930_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_930_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_930_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_930_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_unbox(v_a_818_);
lean_inc(v_declName_785_);
v___x_823_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_785_, v___x_822_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_921_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_921_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_921_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_921_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 1)
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_920_; 
v_val_833_ = lean_ctor_get(v_a_824_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_920_ == 0)
{
v___x_835_ = v_a_824_;
v_isShared_836_ = v_isSharedCheck_920_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v_a_824_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_920_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
uint8_t v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_unbox(v_a_818_);
lean_dec(v_a_818_);
v___x_838_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
lean_del_object(v___x_826_);
v___x_839_ = lean_array_get_size(v_args_787_);
v___x_840_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_833_);
lean_dec(v_val_833_);
v___x_841_ = lean_nat_dec_lt(v___x_839_, v___x_840_);
lean_dec(v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_del_object(v___x_835_);
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v___x_842_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_842_);
v___x_844_ = v___x_820_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_846_; 
lean_del_object(v___x_820_);
lean_inc_ref(v_type_784_);
v___x_846_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_838_, v_type_784_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; size_t v_sz_848_; size_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc_n(v_a_847_, 2);
lean_dec_ref_known(v___x_846_, 1);
v_sz_848_ = lean_array_size(v_a_847_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_848_, v___x_849_, v_a_847_);
v___x_851_ = l_Array_append___redArg(v_args_787_, v___x_850_);
lean_dec_ref(v___x_850_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___x_851_);
v___x_853_ = v___x_789_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_declName_785_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_us_786_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v___x_851_);
v___x_853_ = v_reuseFailAlloc_911_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_855_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_838_, v___x_853_, v___x_854_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v_fvarId_857_; lean_object* v___x_859_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v_fvarId_857_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_fvarId_857_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 5);
lean_ctor_set(v___x_814_, 0, v_fvarId_857_);
v___x_859_ = v___x_814_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fvarId_857_);
v___x_859_ = v_reuseFailAlloc_902_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_a_856_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5));
v___x_862_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_847_, v___x_860_, v___x_861_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_fvarId_864_; lean_object* v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v_fvarId_864_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_fvarId_864_);
lean_inc(v_fvarId_783_);
v___x_865_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_783_, v_fvarId_864_, v_a_771_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_769_, v_a_771_, v_a_774_);
lean_dec_ref(v_letDecl_769_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v___x_866_, 0);
lean_dec(v_unused_877_);
v___x_868_ = v___x_866_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_dec(v___x_866_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_a_863_);
v___x_871_ = v___x_835_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_863_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_863_);
lean_del_object(v___x_835_);
v_a_878_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_866_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_866_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_863_);
lean_del_object(v___x_835_);
lean_dec_ref(v_letDecl_769_);
v_a_886_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_865_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_865_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_835_);
lean_dec_ref(v_letDecl_769_);
v_a_894_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_862_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_862_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_847_);
lean_del_object(v___x_835_);
lean_del_object(v___x_814_);
lean_dec_ref(v_letDecl_769_);
v_a_903_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_855_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_855_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_835_);
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v_a_912_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_846_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_846_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
else
{
lean_del_object(v___x_835_);
lean_dec(v_val_833_);
lean_del_object(v___x_820_);
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
goto v___jp_828_;
}
}
}
else
{
lean_dec(v_a_824_);
lean_del_object(v___x_820_);
lean_dec(v_a_818_);
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_del_object(v___x_820_);
lean_dec(v_a_818_);
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v_a_922_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_823_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_823_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v_a_931_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_817_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_817_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_941_; 
lean_del_object(v___x_814_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v___x_939_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_939_);
v___x_941_ = v___x_810_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v_a_946_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_797_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_797_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v___x_794_);
lean_del_object(v___x_789_);
lean_dec_ref(v_args_787_);
lean_dec(v_us_786_);
lean_dec(v_declName_785_);
lean_dec_ref(v_letDecl_769_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_value_782_);
lean_dec_ref(v_letDecl_769_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* v_letDecl_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t v___x_969_, size_t v_sz_970_, size_t v_i_971_, lean_object* v_bs_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_970_, v_i_971_, v_bs_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* v___x_974_, lean_object* v_sz_975_, lean_object* v_i_976_, lean_object* v_bs_977_){
_start:
{
uint8_t v___x_24447__boxed_978_; size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v___x_24447__boxed_978_ = lean_unbox(v___x_974_);
v_sz_boxed_979_ = lean_unbox_usize(v_sz_975_);
lean_dec(v_sz_975_);
v_i_boxed_980_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24447__boxed_978_, v_sz_boxed_979_, v_i_boxed_980_, v_bs_977_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* v_c_982_, lean_object* v_fvarId_983_, lean_object* v_a_984_){
_start:
{
if (lean_obj_tag(v_c_982_) == 5)
{
lean_object* v_fvarId_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1008_; 
v_fvarId_986_ = lean_ctor_get(v_c_982_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_c_982_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_988_ = v_c_982_;
v_isShared_989_ = v_isSharedCheck_1008_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_fvarId_986_);
lean_dec(v_c_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1008_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v_subst_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_st_ref_get(v_a_984_);
v_subst_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_ref(v_subst_991_);
lean_dec(v___x_990_);
v___x_992_ = 0;
v___x_993_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_991_, v_fvarId_986_, v___x_992_);
lean_dec_ref(v_subst_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_fvarId_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_988_);
v_fvarId_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_fvarId_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_998_ = l_Lean_instBEqFVarId_beq(v_fvarId_994_, v_fvarId_983_);
lean_dec(v_fvarId_994_);
v___x_999_ = lean_box(v___x_998_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(v___x_992_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 0);
lean_ctor_set(v___x_988_, 0, v___x_1004_);
v___x_1006_ = v___x_988_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v_c_982_);
v___x_1009_ = 0;
v___x_1010_ = lean_box(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* v_c_1012_, lean_object* v_fvarId_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_1012_, v_fvarId_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec(v_fvarId_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* v_c_1017_, lean_object* v_fvarId_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_1017_, v_fvarId_1018_, v_a_1020_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* v_c_1028_, lean_object* v_fvarId_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_1028_, v_fvarId_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_fvarId_1029_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* v_value_1039_){
_start:
{
if (lean_obj_tag(v_value_1039_) == 4)
{
lean_object* v_fvarId_1044_; lean_object* v_args_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_fvarId_1044_ = lean_ctor_get(v_value_1039_, 0);
v_args_1045_ = lean_ctor_get(v_value_1039_, 1);
v___x_1046_ = lean_array_get_size(v_args_1045_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_nat_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
goto v___jp_1041_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_inc(v_fvarId_1044_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_fvarId_1044_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
else
{
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* v_value_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_1051_);
lean_dec(v_value_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* v_value_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_1054_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* v_value_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_value_1064_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* v_a_1074_, lean_object* v___x_1075_, lean_object* v_fvarId_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_fvarId_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_fvarId_1082_ = lean_ctor_get(v_a_1074_, 0);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_fvarId_1076_);
v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1075_);
v___x_1085_ = lean_array_push(v___x_1084_, v___x_1083_);
lean_inc(v_fvarId_1082_);
v___x_1086_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_fvarId_1082_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* v_a_1088_, lean_object* v___x_1089_, lean_object* v_fvarId_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_1088_, v___x_1089_, v_fvarId_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___x_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t v_pu_1097_, uint8_t v_t_1098_, lean_object* v_args_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_subst_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_subst_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_subst_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_1097_, v_subst_1103_, v_args_1099_, v_t_1098_);
lean_dec_ref(v_subst_1103_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* v_pu_1106_, lean_object* v_t_1107_, lean_object* v_args_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v_pu_boxed_1111_; uint8_t v_t_boxed_1112_; lean_object* v_res_1113_; 
v_pu_boxed_1111_ = lean_unbox(v_pu_1106_);
v_t_boxed_1112_ = lean_unbox(v_t_1107_);
v_res_1113_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_boxed_1111_, v_t_boxed_1112_, v_args_1108_, v___y_1109_);
lean_dec(v___y_1109_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* v_as_1114_, size_t v_i_1115_, size_t v_stop_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_usize_dec_eq(v_i_1115_, v_stop_1116_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_array_uget_borrowed(v_as_1114_, v_i_1115_);
lean_inc(v___x_1121_);
v___x_1122_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_1121_, v___y_1118_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; size_t v___x_1124_; size_t v___x_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1115_, v___x_1124_);
v_i_1115_ = v___x_1125_;
v_b_1117_ = v_a_1123_;
goto _start;
}
else
{
return v___x_1122_;
}
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_b_1117_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* v_as_1128_, lean_object* v_i_1129_, lean_object* v_stop_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
size_t v_i_boxed_1134_; size_t v_stop_boxed_1135_; lean_object* v_res_1136_; 
v_i_boxed_1134_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_stop_boxed_1135_ = lean_unbox_usize(v_stop_1130_);
lean_dec(v_stop_1130_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_1128_, v_i_boxed_1134_, v_stop_boxed_1135_, v_b_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v_as_1128_);
return v_res_1136_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v_as_1137_, size_t v_i_1138_, size_t v_stop_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_eq(v_i_1138_, v_stop_1139_);
if (v___x_1140_ == 0)
{
uint8_t v___x_1141_; lean_object* v___y_1143_; lean_object* v___x_1147_; 
v___x_1141_ = 1;
v___x_1147_ = lean_array_uget_borrowed(v_as_1137_, v_i_1138_);
switch(lean_obj_tag(v___x_1147_))
{
case 0:
{
lean_object* v_code_1148_; 
v_code_1148_ = lean_ctor_get(v___x_1147_, 2);
v___y_1143_ = v_code_1148_;
goto v___jp_1142_;
}
case 1:
{
lean_object* v_code_1149_; 
v_code_1149_ = lean_ctor_get(v___x_1147_, 1);
v___y_1143_ = v_code_1149_;
goto v___jp_1142_;
}
default: 
{
lean_object* v_code_1150_; 
v_code_1150_ = lean_ctor_get(v___x_1147_, 0);
v___y_1143_ = v_code_1150_;
goto v___jp_1142_;
}
}
v___jp_1142_:
{
if (lean_obj_tag(v___y_1143_) == 6)
{
if (v___x_1140_ == 0)
{
size_t v___x_1144_; size_t v___x_1145_; 
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1138_, v___x_1144_);
v_i_1138_ = v___x_1145_;
goto _start;
}
else
{
return v___x_1141_;
}
}
else
{
return v___x_1141_;
}
}
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v_as_1152_, lean_object* v_i_1153_, lean_object* v_stop_1154_){
_start:
{
size_t v_i_boxed_1155_; size_t v_stop_boxed_1156_; uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_i_boxed_1155_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_stop_boxed_1156_ = lean_unbox_usize(v_stop_1154_);
lean_dec(v_stop_1154_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_1152_, v_i_boxed_1155_, v_stop_boxed_1156_);
lean_dec_ref(v_as_1152_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1159_, uint8_t v_t_1160_, lean_object* v_i_1161_, lean_object* v_as_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_array_get_size(v_as_1162_);
v___x_1167_ = lean_nat_dec_lt(v_i_1161_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec(v_i_1161_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_as_1162_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v_type_1170_; lean_object* v___x_1171_; lean_object* v_subst_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1169_ = lean_array_fget_borrowed(v_as_1162_, v_i_1161_);
v_type_1170_ = lean_ctor_get(v_a_1169_, 2);
v___x_1171_ = lean_st_ref_get(v___y_1163_);
v_subst_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc_ref(v_subst_1172_);
lean_dec(v___x_1171_);
lean_inc_ref(v_type_1170_);
v___x_1173_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1159_, v_subst_1172_, v_t_1160_, v_type_1170_);
lean_dec_ref(v_subst_1172_);
lean_inc(v_a_1169_);
v___x_1174_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1159_, v_a_1169_, v___x_1173_, v___y_1164_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; size_t v___x_1176_; size_t v___x_1177_; uint8_t v___x_1178_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = lean_ptr_addr(v_a_1169_);
v___x_1177_ = lean_ptr_addr(v_a_1175_);
v___x_1178_ = lean_usize_dec_eq(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_add(v_i_1161_, v___x_1179_);
v___x_1181_ = lean_array_fset(v_as_1162_, v_i_1161_, v_a_1175_);
lean_dec(v_i_1161_);
v_i_1161_ = v___x_1180_;
v_as_1162_ = v___x_1181_;
goto _start;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_a_1175_);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_add(v_i_1161_, v___x_1183_);
lean_dec(v_i_1161_);
v_i_1161_ = v___x_1184_;
goto _start;
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_as_1162_);
lean_dec(v_i_1161_);
v_a_1186_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1174_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1174_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1194_, lean_object* v_t_1195_, lean_object* v_i_1196_, lean_object* v_as_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v_pu_boxed_1201_; uint8_t v_t_boxed_1202_; lean_object* v_res_1203_; 
v_pu_boxed_1201_ = lean_unbox(v_pu_1194_);
v_t_boxed_1202_ = lean_unbox(v_t_1195_);
v_res_1203_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1201_, v_t_boxed_1202_, v_i_1196_, v_as_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1204_, uint8_t v_t_1205_, lean_object* v_ps_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1204_, v_t_1205_, v___x_1215_, v_ps_1206_, v___y_1208_, v___y_1211_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1217_, lean_object* v_t_1218_, lean_object* v_ps_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v_pu_boxed_1228_; uint8_t v_t_boxed_1229_; lean_object* v_res_1230_; 
v_pu_boxed_1228_ = lean_unbox(v_pu_1217_);
v_t_boxed_1229_ = lean_unbox(v_t_1218_);
v_res_1230_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1228_, v_t_boxed_1229_, v_ps_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1231_, uint8_t v_t_1232_, lean_object* v_decl_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_type_1237_; lean_object* v_value_1238_; lean_object* v___x_1239_; lean_object* v_subst_1240_; lean_object* v___x_1241_; lean_object* v_subst_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_type_1237_ = lean_ctor_get(v_decl_1233_, 2);
v_value_1238_ = lean_ctor_get(v_decl_1233_, 3);
v___x_1239_ = lean_st_ref_get(v___y_1234_);
v_subst_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_subst_1240_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_st_ref_get(v___y_1234_);
v_subst_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_subst_1242_);
lean_dec(v___x_1241_);
lean_inc_ref(v_type_1237_);
v___x_1243_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1231_, v_subst_1240_, v_t_1232_, v_type_1237_);
lean_dec_ref(v_subst_1240_);
lean_inc(v_value_1238_);
v___x_1244_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1231_, v_subst_1242_, v_value_1238_, v_t_1232_);
lean_dec_ref(v_subst_1242_);
v___x_1245_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1231_, v_decl_1233_, v___x_1243_, v___x_1244_, v___y_1235_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1246_, lean_object* v_t_1247_, lean_object* v_decl_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_pu_boxed_1252_; uint8_t v_t_boxed_1253_; lean_object* v_res_1254_; 
v_pu_boxed_1252_ = lean_unbox(v_pu_1246_);
v_t_boxed_1253_ = lean_unbox(v_t_1247_);
v_res_1254_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1252_, v_t_boxed_1253_, v_decl_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1255_, size_t v_sz_1256_, size_t v_i_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_b_1258_);
return v___x_1262_;
}
else
{
lean_object* v_array_1263_; lean_object* v_start_1264_; lean_object* v_stop_1265_; uint8_t v___x_1266_; 
v_array_1263_ = lean_ctor_get(v_b_1258_, 0);
v_start_1264_ = lean_ctor_get(v_b_1258_, 1);
v_stop_1265_ = lean_ctor_get(v_b_1258_, 2);
v___x_1266_ = lean_nat_dec_lt(v_start_1264_, v_stop_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1258_);
return v___x_1267_;
}
else
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1361_; 
lean_inc(v_stop_1265_);
lean_inc(v_start_1264_);
lean_inc_ref(v_array_1263_);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_b_1258_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; 
v_unused_1362_ = lean_ctor_get(v_b_1258_, 2);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_b_1258_, 1);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_b_1258_, 0);
lean_dec(v_unused_1364_);
v___x_1269_ = v_b_1258_;
v_isShared_1270_ = v_isSharedCheck_1361_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v_b_1258_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1361_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v_fvarId_1273_; lean_object* v_subst_1274_; lean_object* v_used_1275_; lean_object* v_binderRenaming_1276_; lean_object* v_funDeclInfoMap_1277_; uint8_t v_simplified_1278_; lean_object* v_visited_1279_; lean_object* v_inline_1280_; lean_object* v_inlineLocal_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1360_; 
v___x_1271_ = lean_st_ref_take(v___y_1259_);
v_a_1272_ = lean_array_uget_borrowed(v_as_1255_, v_i_1257_);
v_fvarId_1273_ = lean_ctor_get(v_a_1272_, 0);
v_subst_1274_ = lean_ctor_get(v___x_1271_, 0);
v_used_1275_ = lean_ctor_get(v___x_1271_, 1);
v_binderRenaming_1276_ = lean_ctor_get(v___x_1271_, 2);
v_funDeclInfoMap_1277_ = lean_ctor_get(v___x_1271_, 3);
v_simplified_1278_ = lean_ctor_get_uint8(v___x_1271_, sizeof(void*)*7);
v_visited_1279_ = lean_ctor_get(v___x_1271_, 4);
v_inline_1280_ = lean_ctor_get(v___x_1271_, 5);
v_inlineLocal_1281_ = lean_ctor_get(v___x_1271_, 6);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1283_ = v___x_1271_;
v_isShared_1284_ = v_isSharedCheck_1360_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_inlineLocal_1281_);
lean_inc(v_inline_1280_);
lean_inc(v_visited_1279_);
lean_inc(v_funDeclInfoMap_1277_);
lean_inc(v_binderRenaming_1276_);
lean_inc(v_used_1275_);
lean_inc(v_subst_1274_);
lean_dec(v___x_1271_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1360_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1285_ = lean_array_fget(v_array_1263_, v_start_1264_);
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_nat_add(v_start_1264_, v___x_1286_);
lean_dec(v_start_1264_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1287_);
v___x_1289_ = v___x_1269_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_array_1263_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_stop_1265_);
v___x_1289_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___y_1291_; lean_object* v___y_1300_; lean_object* v_i_1301_; lean_object* v___y_1316_; lean_object* v_i_1317_; lean_object* v___y_1322_; lean_object* v___x_1331_; 
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1274_, v_fvarId_1273_);
switch(lean_obj_tag(v___x_1331_))
{
case 0:
{
lean_object* v_index_1332_; lean_object* v_size_1333_; lean_object* v___x_1334_; 
v_index_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_index_1332_);
lean_dec_ref_known(v___x_1331_, 3);
v_size_1333_ = lean_ctor_get(v_subst_1274_, 0);
lean_inc(v_size_1333_);
lean_inc(v_fvarId_1273_);
v___x_1334_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1274_, v_size_1333_, v_index_1332_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_index_1332_);
v___y_1291_ = v___x_1334_;
goto v___jp_1290_;
}
case 1:
{
lean_object* v_index_1335_; lean_object* v_size_1336_; lean_object* v_keyArray_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_index_1335_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_index_1335_);
lean_dec_ref_known(v___x_1331_, 1);
v_size_1336_ = lean_ctor_get(v_subst_1274_, 0);
v_keyArray_1337_ = lean_ctor_get(v_subst_1274_, 1);
v___x_1338_ = lean_nat_add(v_size_1336_, v___x_1286_);
v___x_1339_ = lean_array_get_size(v_keyArray_1337_);
v___x_1340_ = lean_nat_dec_lt(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec(v___x_1338_);
lean_dec(v_index_1335_);
goto v___jp_1305_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1341_ = lean_unsigned_to_nat(4u);
v___x_1342_ = lean_nat_mul(v___x_1338_, v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(3u);
v___x_1344_ = lean_nat_mul(v___x_1339_, v___x_1343_);
v___x_1345_ = lean_nat_dec_le(v___x_1342_, v___x_1344_);
lean_dec(v___x_1344_);
lean_dec(v___x_1342_);
if (v___x_1345_ == 0)
{
lean_dec(v___x_1338_);
lean_dec(v_index_1335_);
goto v___jp_1305_;
}
else
{
lean_object* v___x_1346_; 
lean_inc(v_fvarId_1273_);
v___x_1346_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_1274_, v___x_1338_, v_index_1335_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_index_1335_);
v___y_1291_ = v___x_1346_;
goto v___jp_1290_;
}
}
}
default: 
{
lean_object* v_size_1347_; lean_object* v_keyArray_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_size_1347_ = lean_ctor_get(v_subst_1274_, 0);
v_keyArray_1348_ = lean_ctor_get(v_subst_1274_, 1);
v___x_1349_ = lean_nat_add(v_size_1347_, v___x_1286_);
v___x_1350_ = lean_array_get_size(v_keyArray_1348_);
v___x_1351_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v___x_1349_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_subst_1274_);
lean_dec_ref(v_subst_1274_);
v___y_1322_ = v___x_1352_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = lean_nat_mul(v___x_1349_, v___x_1353_);
lean_dec(v___x_1349_);
v___x_1355_ = lean_unsigned_to_nat(3u);
v___x_1356_ = lean_nat_mul(v___x_1350_, v___x_1355_);
v___x_1357_ = lean_nat_dec_le(v___x_1354_, v___x_1356_);
lean_dec(v___x_1356_);
lean_dec(v___x_1354_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_subst_1274_);
lean_dec_ref(v_subst_1274_);
v___y_1322_ = v___x_1358_;
goto v___jp_1321_;
}
else
{
v___y_1322_ = v_subst_1274_;
goto v___jp_1321_;
}
}
}
}
v___jp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___y_1291_);
v___x_1293_ = v___x_1283_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___y_1291_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_used_1275_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_binderRenaming_1276_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_funDeclInfoMap_1277_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_visited_1279_);
lean_ctor_set(v_reuseFailAlloc_1298_, 5, v_inline_1280_);
lean_ctor_set(v_reuseFailAlloc_1298_, 6, v_inlineLocal_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*7, v_simplified_1278_);
v___x_1293_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; 
v___x_1294_ = lean_st_ref_put(v___y_1259_, v___x_1293_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1257_, v___x_1295_);
v_i_1257_ = v___x_1296_;
v_b_1258_ = v___x_1289_;
goto _start;
}
}
v___jp_1299_:
{
lean_object* v_size_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_size_1302_ = lean_ctor_get(v___y_1300_, 0);
v___x_1303_ = lean_nat_add(v_size_1302_, v___x_1286_);
lean_inc(v_fvarId_1273_);
v___x_1304_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1300_, v___x_1303_, v_i_1301_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_i_1301_);
v___y_1291_ = v___x_1304_;
goto v___jp_1290_;
}
v___jp_1305_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_subst_1274_);
lean_dec_ref(v_subst_1274_);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___x_1306_, v_fvarId_1273_);
switch(lean_obj_tag(v___x_1307_))
{
case 0:
{
lean_object* v_index_1308_; lean_object* v_size_1309_; lean_object* v___x_1310_; 
v_index_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_index_1308_);
lean_dec_ref_known(v___x_1307_, 3);
v_size_1309_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_size_1309_);
lean_inc(v_fvarId_1273_);
v___x_1310_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1306_, v_size_1309_, v_index_1308_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_index_1308_);
v___y_1291_ = v___x_1310_;
goto v___jp_1290_;
}
case 1:
{
lean_object* v_index_1311_; 
v_index_1311_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_index_1311_);
lean_dec_ref_known(v___x_1307_, 1);
v___y_1300_ = v___x_1306_;
v_i_1301_ = v_index_1311_;
goto v___jp_1299_;
}
default: 
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1306_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_index_1314_; 
v_index_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_index_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___y_1300_ = v___x_1306_;
v_i_1301_ = v_index_1314_;
goto v___jp_1299_;
}
else
{
lean_dec(v___x_1285_);
v___y_1291_ = v___x_1306_;
goto v___jp_1290_;
}
}
}
}
v___jp_1315_:
{
lean_object* v_size_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_size_1318_ = lean_ctor_get(v___y_1316_, 0);
v___x_1319_ = lean_nat_add(v_size_1318_, v___x_1286_);
lean_inc(v_fvarId_1273_);
v___x_1320_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1316_, v___x_1319_, v_i_1317_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_i_1317_);
v___y_1291_ = v___x_1320_;
goto v___jp_1290_;
}
v___jp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___y_1322_, v_fvarId_1273_);
switch(lean_obj_tag(v___x_1323_))
{
case 0:
{
lean_object* v_index_1324_; lean_object* v_size_1325_; lean_object* v___x_1326_; 
v_index_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_index_1324_);
lean_dec_ref_known(v___x_1323_, 3);
v_size_1325_ = lean_ctor_get(v___y_1322_, 0);
lean_inc(v_size_1325_);
lean_inc(v_fvarId_1273_);
v___x_1326_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1322_, v_size_1325_, v_index_1324_, v_fvarId_1273_, v___x_1285_);
lean_dec(v_index_1324_);
v___y_1291_ = v___x_1326_;
goto v___jp_1290_;
}
case 1:
{
lean_object* v_index_1327_; 
v_index_1327_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_index_1327_);
lean_dec_ref_known(v___x_1323_, 1);
v___y_1316_ = v___y_1322_;
v_i_1317_ = v_index_1327_;
goto v___jp_1315_;
}
default: 
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1322_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_index_1330_; 
v_index_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_index_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___y_1316_ = v___y_1322_;
v_i_1317_ = v_index_1330_;
goto v___jp_1315_;
}
else
{
lean_dec(v___x_1285_);
v___y_1291_ = v___y_1322_;
goto v___jp_1290_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1365_, lean_object* v_sz_1366_, lean_object* v_i_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
size_t v_sz_boxed_1371_; size_t v_i_boxed_1372_; lean_object* v_res_1373_; 
v_sz_boxed_1371_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v_i_boxed_1372_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1365_, v_sz_boxed_1371_, v_i_boxed_1372_, v_b_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v_as_1365_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1374_, lean_object* v___f_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v_fvarId_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
lean_inc(v_fvarId_1378_);
v___x_1384_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1378_, v___y_1374_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; 
lean_dec_ref_known(v___x_1384_, 1);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1376_);
v___x_1385_ = lean_apply_9(v___f_1375_, v_fvarId_1378_, v___y_1376_, v___y_1374_, v___y_1377_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, lean_box(0));
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_fvarId_1378_);
lean_dec_ref(v___f_1375_);
v_a_1386_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1384_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1394_, lean_object* v___f_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v_fvarId_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1394_, v___f_1395_, v___y_1396_, v___y_1397_, v_fvarId_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1394_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
lean_object* v_ks_1409_; lean_object* v_vs_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1434_; 
v_ks_1409_ = lean_ctor_get(v_x_1405_, 0);
v_vs_1410_ = lean_ctor_get(v_x_1405_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1405_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1412_ = v_x_1405_;
v_isShared_1413_ = v_isSharedCheck_1434_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_vs_1410_);
lean_inc(v_ks_1409_);
lean_dec(v_x_1405_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1434_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_array_get_size(v_ks_1409_);
v___x_1415_ = lean_nat_dec_lt(v_x_1406_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec(v_x_1406_);
v___x_1416_ = lean_array_push(v_ks_1409_, v_x_1407_);
v___x_1417_ = lean_array_push(v_vs_1410_, v_x_1408_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1417_);
lean_ctor_set(v___x_1412_, 0, v___x_1416_);
v___x_1419_ = v___x_1412_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v_k_x27_1421_; uint8_t v___x_1422_; 
v_k_x27_1421_ = lean_array_fget_borrowed(v_ks_1409_, v_x_1406_);
v___x_1422_ = lean_name_eq(v_x_1407_, v_k_x27_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; 
if (v_isShared_1413_ == 0)
{
v___x_1424_ = v___x_1412_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_ks_1409_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_vs_1410_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v_x_1406_, v___x_1425_);
lean_dec(v_x_1406_);
v_x_1405_ = v___x_1424_;
v_x_1406_ = v___x_1426_;
goto _start;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = lean_array_fset(v_ks_1409_, v_x_1406_, v_x_1407_);
v___x_1430_ = lean_array_fset(v_vs_1410_, v_x_1406_, v_x_1408_);
lean_dec(v_x_1406_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1430_);
lean_ctor_set(v___x_1412_, 0, v___x_1429_);
v___x_1432_ = v___x_1412_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1435_, lean_object* v_k_1436_, lean_object* v_v_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1435_, v___x_1438_, v_k_1436_, v_v_1437_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1441_, size_t v_x_1442_, size_t v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1441_) == 0)
{
lean_object* v_es_1446_; size_t v___x_1447_; size_t v___x_1448_; lean_object* v_j_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_es_1446_ = lean_ctor_get(v_x_1441_, 0);
v___x_1447_ = ((size_t)31ULL);
v___x_1448_ = lean_usize_land(v_x_1442_, v___x_1447_);
v_j_1449_ = lean_usize_to_nat(v___x_1448_);
v___x_1450_ = lean_array_get_size(v_es_1446_);
v___x_1451_ = lean_nat_dec_lt(v_j_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec(v_j_1449_);
lean_dec(v_x_1445_);
lean_dec(v_x_1444_);
return v_x_1441_;
}
else
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1490_; 
lean_inc_ref(v_es_1446_);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1441_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v_x_1441_, 0);
lean_dec(v_unused_1491_);
v___x_1453_ = v_x_1441_;
v_isShared_1454_ = v_isSharedCheck_1490_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_x_1441_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1490_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_v_1455_; lean_object* v___x_1456_; lean_object* v_xs_x27_1457_; lean_object* v___y_1459_; 
v_v_1455_ = lean_array_fget(v_es_1446_, v_j_1449_);
v___x_1456_ = lean_box(0);
v_xs_x27_1457_ = lean_array_fset(v_es_1446_, v_j_1449_, v___x_1456_);
switch(lean_obj_tag(v_v_1455_))
{
case 0:
{
lean_object* v_key_1464_; lean_object* v_val_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1475_; 
v_key_1464_ = lean_ctor_get(v_v_1455_, 0);
v_val_1465_ = lean_ctor_get(v_v_1455_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_v_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1467_ = v_v_1455_;
v_isShared_1468_ = v_isSharedCheck_1475_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_val_1465_);
lean_inc(v_key_1464_);
lean_dec(v_v_1455_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1475_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_name_eq(v_x_1444_, v_key_1464_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_del_object(v___x_1467_);
v___x_1470_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1464_, v_val_1465_, v_x_1444_, v_x_1445_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
v___y_1459_ = v___x_1471_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_val_1465_);
lean_dec(v_key_1464_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_x_1445_);
lean_ctor_set(v___x_1467_, 0, v_x_1444_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_x_1444_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_x_1445_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
v___y_1459_ = v___x_1473_;
goto v___jp_1458_;
}
}
}
}
case 1:
{
lean_object* v_node_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1488_; 
v_node_1476_ = lean_ctor_get(v_v_1455_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_v_1455_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1478_ = v_v_1455_;
v_isShared_1479_ = v_isSharedCheck_1488_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_node_1476_);
lean_dec(v_v_1455_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1488_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1480_ = ((size_t)5ULL);
v___x_1481_ = lean_usize_shift_right(v_x_1442_, v___x_1480_);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_add(v_x_1443_, v___x_1482_);
v___x_1484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1476_, v___x_1481_, v___x_1483_, v_x_1444_, v_x_1445_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1484_);
v___x_1486_ = v___x_1478_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v___y_1459_ = v___x_1486_;
goto v___jp_1458_;
}
}
}
default: 
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_x_1444_);
lean_ctor_set(v___x_1489_, 1, v_x_1445_);
v___y_1459_ = v___x_1489_;
goto v___jp_1458_;
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_array_fset(v_xs_x27_1457_, v_j_1449_, v___y_1459_);
lean_dec(v_j_1449_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1460_);
v___x_1462_ = v___x_1453_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_ks_1492_; lean_object* v_vs_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1513_; 
v_ks_1492_ = lean_ctor_get(v_x_1441_, 0);
v_vs_1493_ = lean_ctor_get(v_x_1441_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1441_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1495_ = v_x_1441_;
v_isShared_1496_ = v_isSharedCheck_1513_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_vs_1493_);
lean_inc(v_ks_1492_);
lean_dec(v_x_1441_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1513_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_ks_1492_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_vs_1493_);
v___x_1498_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v_newNode_1499_; uint8_t v___y_1501_; size_t v___x_1507_; uint8_t v___x_1508_; 
v_newNode_1499_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1498_, v_x_1444_, v_x_1445_);
v___x_1507_ = ((size_t)7ULL);
v___x_1508_ = lean_usize_dec_le(v___x_1507_, v_x_1443_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1499_);
v___x_1510_ = lean_unsigned_to_nat(4u);
v___x_1511_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
lean_dec(v___x_1509_);
v___y_1501_ = v___x_1511_;
goto v___jp_1500_;
}
else
{
v___y_1501_ = v___x_1508_;
goto v___jp_1500_;
}
v___jp_1500_:
{
if (v___y_1501_ == 0)
{
lean_object* v_ks_1502_; lean_object* v_vs_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_ks_1502_ = lean_ctor_get(v_newNode_1499_, 0);
lean_inc_ref(v_ks_1502_);
v_vs_1503_ = lean_ctor_get(v_newNode_1499_, 1);
lean_inc_ref(v_vs_1503_);
lean_dec_ref(v_newNode_1499_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1443_, v_ks_1502_, v_vs_1503_, v___x_1504_, v___x_1505_);
lean_dec_ref(v_vs_1503_);
lean_dec_ref(v_ks_1502_);
return v___x_1506_;
}
else
{
return v_newNode_1499_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1514_, lean_object* v_keys_1515_, lean_object* v_vals_1516_, lean_object* v_i_1517_, lean_object* v_entries_1518_){
_start:
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = lean_array_get_size(v_keys_1515_);
v___x_1520_ = lean_nat_dec_lt(v_i_1517_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_dec(v_i_1517_);
return v_entries_1518_;
}
else
{
lean_object* v_k_1521_; lean_object* v_v_1522_; uint64_t v___y_1524_; 
v_k_1521_ = lean_array_fget_borrowed(v_keys_1515_, v_i_1517_);
v_v_1522_ = lean_array_fget_borrowed(v_vals_1516_, v_i_1517_);
if (lean_obj_tag(v_k_1521_) == 0)
{
uint64_t v___x_1535_; 
v___x_1535_ = 1723ULL;
v___y_1524_ = v___x_1535_;
goto v___jp_1523_;
}
else
{
uint64_t v_hash_1536_; 
v_hash_1536_ = lean_ctor_get_uint64(v_k_1521_, sizeof(void*)*2);
v___y_1524_ = v_hash_1536_;
goto v___jp_1523_;
}
v___jp_1523_:
{
size_t v_h_1525_; size_t v___x_1526_; lean_object* v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v_h_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_h_1525_ = lean_uint64_to_usize(v___y_1524_);
v___x_1526_ = ((size_t)5ULL);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_sub(v_depth_1514_, v___x_1528_);
v___x_1530_ = lean_usize_mul(v___x_1526_, v___x_1529_);
v_h_1531_ = lean_usize_shift_right(v_h_1525_, v___x_1530_);
v___x_1532_ = lean_nat_add(v_i_1517_, v___x_1527_);
lean_dec(v_i_1517_);
lean_inc(v_v_1522_);
lean_inc(v_k_1521_);
v___x_1533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1518_, v_h_1531_, v_depth_1514_, v_k_1521_, v_v_1522_);
v_i_1517_ = v___x_1532_;
v_entries_1518_ = v___x_1533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1537_, lean_object* v_keys_1538_, lean_object* v_vals_1539_, lean_object* v_i_1540_, lean_object* v_entries_1541_){
_start:
{
size_t v_depth_boxed_1542_; lean_object* v_res_1543_; 
v_depth_boxed_1542_ = lean_unbox_usize(v_depth_1537_);
lean_dec(v_depth_1537_);
v_res_1543_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1542_, v_keys_1538_, v_vals_1539_, v_i_1540_, v_entries_1541_);
lean_dec_ref(v_vals_1539_);
lean_dec_ref(v_keys_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
size_t v_x_52239__boxed_1549_; size_t v_x_52240__boxed_1550_; lean_object* v_res_1551_; 
v_x_52239__boxed_1549_ = lean_unbox_usize(v_x_1545_);
lean_dec(v_x_1545_);
v_x_52240__boxed_1550_ = lean_unbox_usize(v_x_1546_);
lean_dec(v_x_1546_);
v_res_1551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1544_, v_x_52239__boxed_1549_, v_x_52240__boxed_1550_, v_x_1547_, v_x_1548_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_){
_start:
{
uint64_t v___y_1556_; 
if (lean_obj_tag(v_x_1553_) == 0)
{
uint64_t v___x_1560_; 
v___x_1560_ = 1723ULL;
v___y_1556_ = v___x_1560_;
goto v___jp_1555_;
}
else
{
uint64_t v_hash_1561_; 
v_hash_1561_ = lean_ctor_get_uint64(v_x_1553_, sizeof(void*)*2);
v___y_1556_ = v_hash_1561_;
goto v___jp_1555_;
}
v___jp_1555_:
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_uint64_to_usize(v___y_1556_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1552_, v___x_1557_, v___x_1558_, v_x_1553_, v_x_1554_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1562_, lean_object* v_b_1563_){
_start:
{
lean_object* v_array_1564_; lean_object* v_start_1565_; lean_object* v_stop_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1579_; 
v_array_1564_ = lean_ctor_get(v_a_1562_, 0);
v_start_1565_ = lean_ctor_get(v_a_1562_, 1);
v_stop_1566_ = lean_ctor_get(v_a_1562_, 2);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1568_ = v_a_1562_;
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_stop_1566_);
lean_inc(v_start_1565_);
lean_inc(v_array_1564_);
lean_dec(v_a_1562_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1579_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_nat_dec_lt(v_start_1565_, v_stop_1566_);
if (v___x_1570_ == 0)
{
lean_del_object(v___x_1568_);
lean_dec(v_stop_1566_);
lean_dec(v_start_1565_);
lean_dec_ref(v_array_1564_);
return v_b_1563_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_nat_add(v_start_1565_, v___x_1571_);
lean_inc_ref(v_array_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1572_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_array_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_stop_1566_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_array_fget(v_array_1564_, v_start_1565_);
lean_dec(v_start_1565_);
lean_dec_ref(v_array_1564_);
v___x_1576_ = lean_array_push(v_b_1563_, v___x_1575_);
v_a_1562_ = v___x_1574_;
v_b_1563_ = v___x_1576_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1580_, size_t v_i_1581_, size_t v_stop_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_usize_dec_eq(v_i_1581_, v_stop_1582_);
if (v___x_1586_ == 0)
{
uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = 0;
v___x_1588_ = lean_array_uget_borrowed(v_as_1580_, v_i_1581_);
v___x_1589_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1587_, v___x_1588_, v___y_1584_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; size_t v___x_1591_; size_t v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1581_, v___x_1591_);
v_i_1581_ = v___x_1592_;
v_b_1583_ = v_a_1590_;
goto _start;
}
else
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_b_1583_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1595_, lean_object* v_i_1596_, lean_object* v_stop_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
size_t v_i_boxed_1601_; size_t v_stop_boxed_1602_; lean_object* v_res_1603_; 
v_i_boxed_1601_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_stop_boxed_1602_ = lean_unbox_usize(v_stop_1597_);
lean_dec(v_stop_1597_);
v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1595_, v_i_boxed_1601_, v_stop_boxed_1602_, v_b_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v_as_1595_);
return v_res_1603_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = 0;
v___x_1605_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1608_ = lean_panic_fn_borrowed(v___x_1607_, v_msg_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1609_, size_t v_i_1610_, size_t v_stop_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_eq(v_i_1610_, v_stop_1611_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v_type_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_array_uget_borrowed(v_as_1609_, v_i_1610_);
v_type_1616_ = lean_ctor_get(v___x_1615_, 2);
v___x_1617_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1616_, v___y_1612_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1629_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_unbox(v_a_1618_);
if (v___x_1622_ == 0)
{
size_t v___x_1623_; size_t v___x_1624_; 
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_add(v_i_1610_, v___x_1623_);
v_i_1610_ = v___x_1624_;
goto _start;
}
else
{
lean_object* v___x_1627_; 
if (v_isShared_1621_ == 0)
{
v___x_1627_ = v___x_1620_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1618_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
return v___x_1617_;
}
}
else
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = 0;
v___x_1631_ = lean_box(v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1633_, lean_object* v_i_1634_, lean_object* v_stop_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_i_boxed_1638_; size_t v_stop_boxed_1639_; lean_object* v_res_1640_; 
v_i_boxed_1638_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_stop_boxed_1639_ = lean_unbox_usize(v_stop_1635_);
lean_dec(v_stop_1635_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1633_, v_i_boxed_1638_, v_stop_boxed_1639_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v_as_1633_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1641_, size_t v_i_1642_, size_t v_stop_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_usize_dec_eq(v_i_1642_, v_stop_1643_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = 0;
v___x_1649_ = lean_array_uget_borrowed(v_as_1641_, v_i_1642_);
v___x_1650_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1648_, v___x_1649_, v___y_1645_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; size_t v___x_1652_; size_t v___x_1653_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1642_, v___x_1652_);
v_i_1642_ = v___x_1653_;
v_b_1644_ = v_a_1651_;
goto _start;
}
else
{
return v___x_1650_;
}
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_b_1644_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1656_, lean_object* v_i_1657_, lean_object* v_stop_1658_, lean_object* v_b_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
size_t v_i_boxed_1662_; size_t v_stop_boxed_1663_; lean_object* v_res_1664_; 
v_i_boxed_1662_ = lean_unbox_usize(v_i_1657_);
lean_dec(v_i_1657_);
v_stop_boxed_1663_ = lean_unbox_usize(v_stop_1658_);
lean_dec(v_stop_1658_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1656_, v_i_boxed_1662_, v_stop_boxed_1663_, v_b_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v_as_1656_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1665_, size_t v_i_1666_, size_t v_stop_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_a_1675_; lean_object* v___y_1680_; uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_eq(v_i_1666_, v_stop_1667_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_array_uget_borrowed(v_as_1665_, v_i_1666_);
v___x_1685_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1684_);
v___x_1686_ = lean_array_get_size(v___x_1685_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_nat_dec_lt(v___x_1683_, v___x_1686_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v___x_1685_);
v_a_1675_ = v___x_1687_;
goto v___jp_1674_;
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_nat_dec_le(v___x_1686_, v___x_1686_);
if (v___x_1689_ == 0)
{
if (v___x_1688_ == 0)
{
lean_dec_ref(v___x_1685_);
v_a_1675_ = v___x_1687_;
goto v___jp_1674_;
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1686_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1685_, v___x_1690_, v___x_1691_, v___x_1687_, v___y_1670_);
lean_dec_ref(v___x_1685_);
v___y_1680_ = v___x_1692_;
goto v___jp_1679_;
}
}
else
{
size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = lean_usize_of_nat(v___x_1686_);
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1685_, v___x_1693_, v___x_1694_, v___x_1687_, v___y_1670_);
lean_dec_ref(v___x_1685_);
v___y_1680_ = v___x_1695_;
goto v___jp_1679_;
}
}
}
else
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_b_1668_);
return v___x_1696_;
}
v___jp_1674_:
{
size_t v___x_1676_; size_t v___x_1677_; 
v___x_1676_ = ((size_t)1ULL);
v___x_1677_ = lean_usize_add(v_i_1666_, v___x_1676_);
v_i_1666_ = v___x_1677_;
v_b_1668_ = v_a_1675_;
goto _start;
}
v___jp_1679_:
{
if (lean_obj_tag(v___y_1680_) == 0)
{
lean_object* v_a_1681_; 
v_a_1681_ = lean_ctor_get(v___y_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___y_1680_, 1);
v_a_1675_ = v_a_1681_;
goto v___jp_1674_;
}
else
{
return v___y_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1697_, lean_object* v_i_1698_, lean_object* v_stop_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
size_t v_i_boxed_1706_; size_t v_stop_boxed_1707_; lean_object* v_res_1708_; 
v_i_boxed_1706_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_stop_boxed_1707_ = lean_unbox_usize(v_stop_1699_);
lean_dec(v_stop_1699_);
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1697_, v_i_boxed_1706_, v_stop_boxed_1707_, v_b_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_as_1697_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1709_, size_t v_i_1710_, size_t v_stop_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_eq(v_i_1710_, v_stop_1711_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v_fvarId_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_array_uget_borrowed(v_as_1709_, v_i_1710_);
v_fvarId_1716_ = lean_ctor_get(v___x_1715_, 0);
v___x_1717_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1716_, v___y_1712_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1729_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1729_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1729_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_unbox(v_a_1718_);
if (v___x_1722_ == 0)
{
size_t v___x_1723_; size_t v___x_1724_; 
lean_del_object(v___x_1720_);
lean_dec(v_a_1718_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_add(v_i_1710_, v___x_1723_);
v_i_1710_ = v___x_1724_;
goto _start;
}
else
{
lean_object* v___x_1727_; 
if (v_isShared_1721_ == 0)
{
v___x_1727_ = v___x_1720_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1718_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
return v___x_1717_;
}
}
else
{
uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = 0;
v___x_1731_ = lean_box(v___x_1730_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_stop_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
size_t v_i_boxed_1738_; size_t v_stop_boxed_1739_; lean_object* v_res_1740_; 
v_i_boxed_1738_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_stop_boxed_1739_ = lean_unbox_usize(v_stop_1735_);
lean_dec(v_stop_1735_);
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1733_, v_i_boxed_1738_, v_stop_boxed_1739_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v_as_1733_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1745_ = lean_unsigned_to_nat(9u);
v___x_1746_ = lean_unsigned_to_nat(641u);
v___x_1747_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1748_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1749_ = l_mkPanicMessageWithDecl(v___x_1748_, v___x_1747_, v___x_1746_, v___x_1745_, v___x_1744_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1753_, lean_object* v___x_1754_, lean_object* v_fvarId_1755_, lean_object* v_k_1756_, lean_object* v_args_1757_, uint8_t v___x_1758_, lean_object* v___x_1759_, lean_object* v_result_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_lower_1770_; lean_object* v_upper_1771_; uint8_t v___x_1798_; 
v___x_1798_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec(v___x_1759_);
lean_dec_ref(v_args_1757_);
lean_dec(v___x_1754_);
lean_dec(v___x_1753_);
v___x_1799_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1755_, v_result_1760_, v___y_1762_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v___x_1800_; 
lean_dec_ref_known(v___x_1799_, 1);
lean_inc_ref(v___y_1766_);
v___x_1800_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1756_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1800_;
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_k_1756_);
v_a_1801_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1799_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1799_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_nat_dec_le(v___x_1753_, v___x_1759_);
if (v___x_1809_ == 0)
{
lean_dec(v___x_1759_);
v_lower_1770_ = v___x_1753_;
v_upper_1771_ = v___x_1754_;
goto v___jp_1769_;
}
else
{
lean_dec(v___x_1753_);
v_lower_1770_ = v___x_1759_;
v_upper_1771_ = v___x_1754_;
goto v___jp_1769_;
}
}
v___jp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1772_ = l_Array_toSubarray___redArg(v_args_1757_, v_lower_1770_, v_upper_1771_);
v___x_1773_ = l_Subarray_copy___redArg(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_result_1760_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1776_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1758_, v___x_1774_, v___x_1775_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v_fvarId_1778_; lean_object* v___x_1779_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v_fvarId_1778_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_fvarId_1778_);
v___x_1779_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1755_, v_fvarId_1778_, v___y_1762_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec_ref_known(v___x_1779_, 1);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_a_1777_);
lean_ctor_set(v___x_1780_, 1, v_k_1756_);
lean_inc_ref(v___y_1766_);
v___x_1781_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1780_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1781_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v_a_1777_);
lean_dec_ref(v_k_1756_);
v_a_1782_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1779_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1779_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_k_1756_);
lean_dec(v_fvarId_1755_);
v_a_1790_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1776_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1776_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1810_, lean_object* v___x_1811_, lean_object* v_fvarId_1812_, lean_object* v_k_1813_, lean_object* v_args_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v_result_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v___x_52693__boxed_1826_; lean_object* v_res_1827_; 
v___x_52693__boxed_1826_ = lean_unbox(v___x_1815_);
v_res_1827_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1810_, v___x_1811_, v_fvarId_1812_, v_k_1813_, v_args_1814_, v___x_52693__boxed_1826_, v___x_1816_, v_result_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1828_, lean_object* v_k_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_fvarId_1838_; lean_object* v_value_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_2177_; 
v_fvarId_1838_ = lean_ctor_get(v_letDecl_1828_, 0);
v_value_1839_ = lean_ctor_get(v_letDecl_1828_, 3);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_letDecl_1828_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; lean_object* v_unused_2179_; 
v_unused_2178_ = lean_ctor_get(v_letDecl_1828_, 2);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_letDecl_1828_, 1);
lean_dec(v_unused_2179_);
v___x_1841_ = v_letDecl_1828_;
v_isShared_1842_ = v_isSharedCheck_2177_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_value_1839_);
lean_inc(v_fvarId_1838_);
lean_dec(v_letDecl_1828_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_2177_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; 
lean_inc(v_value_1839_);
v___x_1843_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1839_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2168_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_2168_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2168_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
if (lean_obj_tag(v_a_1844_) == 1)
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_1846_);
v_val_1848_ = lean_ctor_get(v_a_1844_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_1844_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_1850_ = v_a_1844_;
v_isShared_1851_ = v_isSharedCheck_2163_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v_a_1844_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_2163_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_params_1852_; lean_object* v_value_1853_; lean_object* v_fType_1854_; lean_object* v_args_1855_; uint8_t v_recursive_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; 
v_params_1852_ = lean_ctor_get(v_val_1848_, 0);
v_value_1853_ = lean_ctor_get(v_val_1848_, 1);
v_fType_1854_ = lean_ctor_get(v_val_1848_, 2);
v_args_1855_ = lean_ctor_get(v_val_1848_, 3);
v_recursive_1856_ = lean_ctor_get_uint8(v_val_1848_, sizeof(void*)*4 + 2);
v___x_1857_ = lean_array_get_size(v_args_1855_);
v___x_1858_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1848_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (lean_obj_tag(v_value_1839_) == 3)
{
lean_object* v_declName_2143_; lean_object* v___x_2144_; 
v_declName_2143_ = lean_ctor_get(v_value_1839_, 0);
lean_inc_n(v_declName_2143_, 2);
lean_dec_ref_known(v_value_1839_, 3);
v___x_2144_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1856_, v_declName_2143_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_declName_2146_; lean_object* v_config_2147_; lean_object* v_inlineStack_2148_; lean_object* v_inlineStackOccs_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_declName_2146_ = lean_ctor_get(v_a_1830_, 0);
v_config_2147_ = lean_ctor_get(v_a_1830_, 1);
v_inlineStack_2148_ = lean_ctor_get(v_a_1830_, 2);
v_inlineStackOccs_2149_ = lean_ctor_get(v_a_1830_, 3);
lean_inc(v_inlineStack_2148_);
lean_inc(v_declName_2143_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_declName_2143_);
lean_ctor_set(v___x_2150_, 1, v_inlineStack_2148_);
lean_inc_ref(v_inlineStackOccs_2149_);
v___x_2151_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_2149_, v_declName_2143_, v_a_2145_);
lean_inc_ref(v_config_2147_);
lean_inc(v_declName_2146_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 3, v___x_2151_);
lean_ctor_set(v___x_1841_, 2, v___x_2150_);
lean_ctor_set(v___x_1841_, 1, v_config_2147_);
lean_ctor_set(v___x_1841_, 0, v_declName_2146_);
v___x_2153_ = v___x_1841_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_declName_2146_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_config_2147_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v___y_2042_ = v___x_2153_;
v___y_2043_ = v_a_1831_;
v___y_2044_ = v_a_1832_;
v___y_2045_ = v_a_1833_;
v___y_2046_ = v_a_1834_;
v___y_2047_ = v_a_1835_;
v___y_2048_ = v_a_1836_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_declName_2143_);
lean_dec(v___x_1858_);
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
lean_del_object(v___x_1841_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
v_a_2155_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2144_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2144_);
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
lean_del_object(v___x_1841_);
lean_dec(v_value_1839_);
lean_inc_ref(v_a_1830_);
v___y_2042_ = v_a_1830_;
v___y_2043_ = v_a_1831_;
v___y_2044_ = v_a_1832_;
v___y_2045_ = v_a_1833_;
v___y_2046_ = v_a_1834_;
v___y_2047_ = v_a_1835_;
v___y_2048_ = v_a_1836_;
goto v___jp_2041_;
}
v___jp_1860_:
{
lean_object* v___x_1874_; 
lean_inc_ref(v___y_1872_);
v___x_1874_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1865_, v___y_1869_, v___y_1862_, v___y_1870_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1862_);
if (lean_obj_tag(v___x_1876_) == 0)
{
uint8_t v___x_1877_; 
lean_dec_ref_known(v___x_1876_, 1);
v___x_1877_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1875_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v___y_1866_);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___y_1861_);
lean_dec(v___y_1861_);
lean_inc_ref(v___x_1878_);
v___x_1879_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1873_, v___x_1878_);
v___x_1880_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1864_, v_fType_1854_, v___x_1879_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc_n(v_a_1881_, 2);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = l_Lean_Expr_headBeta(v_a_1881_);
v___x_1883_ = l_Lean_Expr_isForall(v___x_1882_);
lean_dec_ref(v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref(v___x_1878_);
v___x_1884_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1864_, v_a_1881_, v___x_1859_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_fvarId_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_fvarId_1886_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1872_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1863_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1862_);
lean_inc(v_fvarId_1886_);
v___x_1887_ = lean_apply_9(v___y_1868_, v_fvarId_1886_, v___y_1869_, v___y_1862_, v___y_1870_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_mk_empty_array_with_capacity(v___x_1889_);
v___x_1891_ = lean_array_push(v___x_1890_, v_a_1885_);
v___x_1892_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1893_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1864_, v___x_1891_, v_a_1888_, v___x_1892_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_n(v_a_1894_, 2);
lean_dec_ref_known(v___x_1893_, 1);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1895_, 0, v_a_1894_);
lean_closure_set(v___f_1895_, 1, v___x_1889_);
v___x_1896_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1864_, v_a_1875_, v___f_1895_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1908_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_a_1894_);
lean_ctor_set(v___x_1901_, 1, v_a_1897_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1901_);
v___x_1903_ = v___x_1850_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1903_);
v___x_1905_ = v___x_1899_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1894_);
lean_del_object(v___x_1850_);
v_a_1909_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1896_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1896_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1875_);
lean_del_object(v___x_1850_);
v_a_1917_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1893_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1893_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1885_);
lean_dec(v_a_1875_);
lean_del_object(v___x_1850_);
v_a_1925_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1887_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1887_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1875_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_del_object(v___x_1850_);
v_a_1933_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1884_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1884_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_a_1881_);
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5));
v___x_1942_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1878_, v_a_1875_, v___x_1941_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1943_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v_fvarId_1946_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_fvarId_1946_ = lean_ctor_get(v_a_1945_, 0);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1872_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1863_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1869_);
lean_inc(v_fvarId_1946_);
v___x_1947_ = lean_apply_9(v___y_1868_, v_fvarId_1946_, v___y_1869_, v___y_1862_, v___y_1870_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_a_1945_);
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
v___x_1952_ = lean_array_push(v___x_1951_, v___x_1949_);
v___x_1953_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1952_, v_a_1948_, v___y_1869_, v___y_1862_, v___y_1870_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___x_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1964_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_a_1954_);
v___x_1959_ = v___x_1850_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1959_);
v___x_1961_ = v___x_1956_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_del_object(v___x_1850_);
v_a_1965_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1953_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1953_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1945_);
lean_dec_ref(v___y_1869_);
lean_del_object(v___x_1850_);
v_a_1973_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1947_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1947_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_del_object(v___x_1850_);
v_a_1981_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1944_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1944_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_del_object(v___x_1850_);
v_a_1989_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1942_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1942_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1878_);
lean_dec(v_a_1875_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_del_object(v___x_1850_);
v_a_1997_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1880_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1880_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v___x_2005_; 
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1861_);
lean_dec_ref(v_fType_1854_);
v___x_2005_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1864_, v_a_1875_, v___y_1866_, v___y_1863_, v___y_1871_, v___y_1872_, v___y_1867_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2016_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_a_2006_);
v___x_2011_ = v___x_1850_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2011_);
v___x_2013_ = v___x_2008_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1850_);
v_a_2017_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2005_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2005_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1875_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1861_);
lean_dec_ref(v_fType_1854_);
lean_del_object(v___x_1850_);
v_a_2025_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1876_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1876_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1861_);
lean_dec_ref(v_fType_1854_);
lean_del_object(v___x_1850_);
v_a_2033_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1874_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1874_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
v___jp_2041_:
{
if (v___x_1859_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_inc_ref_n(v_args_1855_, 2);
lean_inc_ref(v_fType_1854_);
lean_inc_ref(v_value_1853_);
lean_inc_ref(v_params_1852_);
lean_dec(v_val_1848_);
v___x_2049_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1858_);
v___x_2050_ = l_Array_toSubarray___redArg(v_args_1855_, v___x_2049_, v___x_1858_);
lean_inc_ref(v___x_2050_);
v___x_2051_ = l_Subarray_copy___redArg(v___x_2050_);
v___x_2052_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1852_, v_value_1853_, v___x_2051_, v___x_1859_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec_ref(v_params_1852_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; uint8_t v___x_2058_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = 0;
v___x_2055_ = lean_box(v___x_2054_);
lean_inc_ref(v_k_1829_);
lean_inc(v_fvarId_1838_);
lean_inc(v___x_1858_);
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_2056_, 0, v___x_1858_);
lean_closure_set(v___f_2056_, 1, v___x_1857_);
lean_closure_set(v___f_2056_, 2, v_fvarId_1838_);
lean_closure_set(v___f_2056_, 3, v_k_1829_);
lean_closure_set(v___f_2056_, 4, v_args_1855_);
lean_closure_set(v___f_2056_, 5, v___x_2055_);
lean_closure_set(v___f_2056_, 6, v___x_2049_);
lean_inc_ref(v___y_2044_);
lean_inc_ref(v___y_2042_);
lean_inc_ref(v___f_2056_);
lean_inc(v___y_2043_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_2057_, 0, v___y_2043_);
lean_closure_set(v___f_2057_, 1, v___f_2056_);
lean_closure_set(v___f_2057_, 2, v___y_2042_);
lean_closure_set(v___f_2057_, 3, v___y_2044_);
v___x_2058_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1829_, v_fvarId_1838_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
if (v___x_2058_ == 0)
{
lean_dec(v___x_1858_);
v___y_1861_ = v___x_2049_;
v___y_1862_ = v___y_2043_;
v___y_1863_ = v___y_2045_;
v___y_1864_ = v___x_2054_;
v___y_1865_ = v_a_2053_;
v___y_1866_ = v___f_2057_;
v___y_1867_ = v___y_2048_;
v___y_1868_ = v___f_2056_;
v___y_1869_ = v___y_2042_;
v___y_1870_ = v___y_2044_;
v___y_1871_ = v___y_2046_;
v___y_1872_ = v___y_2047_;
v___y_1873_ = v___x_2050_;
goto v___jp_1860_;
}
else
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_nat_dec_eq(v___x_1857_, v___x_1858_);
lean_dec(v___x_1858_);
if (v___x_2059_ == 0)
{
v___y_1861_ = v___x_2049_;
v___y_1862_ = v___y_2043_;
v___y_1863_ = v___y_2045_;
v___y_1864_ = v___x_2054_;
v___y_1865_ = v_a_2053_;
v___y_1866_ = v___f_2057_;
v___y_1867_ = v___y_2048_;
v___y_1868_ = v___f_2056_;
v___y_1869_ = v___y_2042_;
v___y_1870_ = v___y_2044_;
v___y_1871_ = v___y_2046_;
v___y_1872_ = v___y_2047_;
v___y_1873_ = v___x_2050_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_2060_; 
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___f_2056_);
lean_dec_ref(v___x_2050_);
lean_dec_ref(v_fType_1854_);
lean_del_object(v___x_1850_);
v___x_2060_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2043_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2060_, 1);
lean_inc_ref(v___y_2047_);
v___x_2061_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_2053_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec_ref(v___y_2042_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_a_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_a_2071_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2061_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_2053_);
lean_dec_ref(v___y_2042_);
v_a_2079_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2060_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2060_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v___x_2050_);
lean_dec_ref(v___y_2042_);
lean_dec(v___x_1858_);
lean_dec_ref(v_args_1855_);
lean_dec_ref(v_fType_1854_);
lean_del_object(v___x_1850_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
v_a_2087_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2052_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2052_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v___x_2095_; 
lean_dec(v___x_1858_);
lean_del_object(v___x_1850_);
v___x_2095_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1848_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_fvarId_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_fvarId_2097_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_fvarId_2097_);
v___x_2098_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1838_, v_fvarId_2097_, v___y_2043_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v___x_2099_; 
lean_dec_ref_known(v___x_2098_, 1);
v___x_2099_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2043_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec_ref_known(v___x_2099_, 1);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_a_2096_);
lean_ctor_set(v___x_2100_, 1, v_k_1829_);
lean_inc_ref(v___y_2047_);
v___x_2101_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_2100_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec_ref(v___y_2042_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2101_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2101_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_k_1829_);
v_a_2119_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2099_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2099_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_k_1829_);
v_a_2127_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2098_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2098_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___y_2042_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
v_a_2135_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2095_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2095_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec(v_a_1844_);
lean_del_object(v___x_1841_);
lean_dec(v_value_1839_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
v___x_2164_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_2164_);
v___x_2166_ = v___x_1846_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_del_object(v___x_1841_);
lean_dec(v_value_1839_);
lean_dec(v_fvarId_1838_);
lean_dec_ref(v_k_1829_);
v_a_2169_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_1843_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_1843_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_typeName_2194_; lean_object* v_discr_2195_; lean_object* v___x_2196_; lean_object* v_subst_2197_; uint8_t v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v_typeName_2194_ = lean_ctor_get(v_cases_2182_, 0);
v_discr_2195_ = lean_ctor_get(v_cases_2182_, 2);
v___x_2196_ = lean_st_ref_get(v_a_2184_);
v_subst_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc_ref(v_subst_2197_);
lean_dec(v___x_2196_);
v___x_2198_ = 0;
v___x_2199_ = 0;
lean_inc(v_discr_2195_);
v___x_2200_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2197_, v_discr_2195_, v___x_2199_);
lean_dec_ref(v_subst_2197_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_fvarId_2201_; lean_object* v___x_2202_; 
v_fvarId_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_fvarId_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_2201_, v_a_2185_, v_a_2187_, v_a_2189_);
lean_dec(v_fvarId_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2432_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2432_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2432_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
if (lean_obj_tag(v_a_2203_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2427_; 
v_val_2207_ = lean_ctor_get(v_a_2203_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_a_2203_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2209_ = v_a_2203_;
v_isShared_2210_ = v_isSharedCheck_2427_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v_a_2203_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2427_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v_env_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = lean_st_ref_get(v_a_2189_);
v_env_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc_ref(v_env_2212_);
lean_dec(v___x_2211_);
v___x_2213_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_2207_);
lean_inc(v___x_2213_);
v___x_2214_ = l_Lean_Environment_find_x3f(v_env_2212_, v___x_2213_, v___x_2199_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2426_; 
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2426_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_val_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2426_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
if (lean_obj_tag(v_val_2215_) == 6)
{
lean_object* v_val_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2425_; 
v_val_2219_ = lean_ctor_get(v_val_2215_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_val_2215_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2221_ = v_val_2215_;
v_isShared_2222_ = v_isSharedCheck_2425_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_val_2219_);
lean_dec(v_val_2215_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2425_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_induct_2223_; uint8_t v___x_2224_; 
v_induct_2223_ = lean_ctor_get(v_val_2219_, 1);
lean_inc(v_induct_2223_);
lean_dec_ref(v_val_2219_);
v___x_2224_ = lean_name_eq(v_typeName_2194_, v_induct_2223_);
lean_dec(v_induct_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_del_object(v___x_2221_);
lean_del_object(v___x_2217_);
lean_dec(v___x_2213_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
lean_dec_ref(v_cases_2182_);
v___x_2225_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2225_);
v___x_2227_ = v___x_2205_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v___x_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2205_);
v___x_2229_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_2198_, v_cases_2182_, v___x_2213_);
v_fst_2230_ = lean_ctor_get(v___x_2229_, 0);
v_snd_2231_ = lean_ctor_get(v___x_2229_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2233_ = v___x_2229_;
v_isShared_2234_ = v_isSharedCheck_2424_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_snd_2231_);
lean_inc(v_fst_2230_);
lean_dec(v___x_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2424_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 4);
lean_ctor_set(v___x_2221_, 0, v_snd_2231_);
v___x_2236_ = v___x_2221_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_snd_2231_);
v___x_2236_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2198_, v___x_2236_, v_a_2187_);
lean_dec_ref(v___x_2236_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2238_; 
lean_dec_ref_known(v___x_2237_, 1);
v___x_2238_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2184_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_fst_2230_) == 0)
{
if (lean_obj_tag(v_val_2207_) == 0)
{
lean_object* v_params_2239_; lean_object* v_code_2240_; lean_object* v_val_2241_; lean_object* v_args_2242_; lean_object* v_lower_2244_; lean_object* v_upper_2245_; lean_object* v_numParams_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
lean_del_object(v___x_2233_);
lean_del_object(v___x_2209_);
v_params_2239_ = lean_ctor_get(v_fst_2230_, 1);
lean_inc_ref(v_params_2239_);
v_code_2240_ = lean_ctor_get(v_fst_2230_, 2);
lean_inc_ref(v_code_2240_);
lean_dec_ref_known(v_fst_2230_, 3);
v_val_2241_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_val_2241_);
v_args_2242_ = lean_ctor_get(v_val_2207_, 1);
lean_inc_ref(v_args_2242_);
lean_dec_ref_known(v_val_2207_, 2);
v_numParams_2288_ = lean_ctor_get(v_val_2241_, 3);
lean_inc(v_numParams_2288_);
lean_dec_ref(v_val_2241_);
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_array_get_size(v_args_2242_);
v___x_2291_ = lean_nat_dec_le(v_numParams_2288_, v___x_2289_);
if (v___x_2291_ == 0)
{
v_lower_2244_ = v_numParams_2288_;
v_upper_2245_ = v___x_2290_;
goto v___jp_2243_;
}
else
{
lean_dec(v_numParams_2288_);
v_lower_2244_ = v___x_2289_;
v_upper_2245_ = v___x_2290_;
goto v___jp_2243_;
}
v___jp_2243_:
{
lean_object* v___x_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2246_ = l_Array_toSubarray___redArg(v_args_2242_, v_lower_2244_, v_upper_2245_);
v_sz_2247_ = lean_array_size(v_params_2239_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2239_, v_sz_2247_, v___x_2248_, v___x_2246_, v_a_2184_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref_known(v___x_2249_, 1);
lean_inc_ref(v_a_2188_);
v___x_2250_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2240_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2252_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v___x_2252_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2198_, v_params_2239_, v_a_2187_);
lean_dec_ref(v_params_2239_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2262_; 
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v___x_2252_, 0);
lean_dec(v_unused_2263_);
v___x_2254_ = v___x_2252_;
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v___x_2252_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2251_);
v___x_2257_ = v___x_2217_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2251_);
v___x_2257_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2259_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2251_);
lean_del_object(v___x_2217_);
v_a_2264_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2252_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2252_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_params_2239_);
lean_del_object(v___x_2217_);
v_a_2272_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2250_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2250_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_code_2240_);
lean_dec_ref(v_params_2239_);
lean_del_object(v___x_2217_);
v_a_2280_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2249_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2249_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
else
{
lean_object* v_params_2292_; lean_object* v_code_2293_; lean_object* v_n_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2385_; 
v_params_2292_ = lean_ctor_get(v_fst_2230_, 1);
lean_inc_ref(v_params_2292_);
v_code_2293_ = lean_ctor_get(v_fst_2230_, 2);
lean_inc_ref(v_code_2293_);
lean_dec_ref_known(v_fst_2230_, 3);
v_n_2294_ = lean_ctor_get(v_val_2207_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_val_2207_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2296_ = v_val_2207_;
v_isShared_2297_ = v_isSharedCheck_2385_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_n_2294_);
lean_dec(v_val_2207_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2385_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_zero_2298_; uint8_t v_isZero_2299_; 
v_zero_2298_ = lean_unsigned_to_nat(0u);
v_isZero_2299_ = lean_nat_dec_eq(v_n_2294_, v_zero_2298_);
if (v_isZero_2299_ == 1)
{
lean_object* v___x_2300_; 
lean_del_object(v___x_2296_);
lean_dec(v_n_2294_);
lean_dec_ref(v_params_2292_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2209_);
lean_inc_ref(v_a_2188_);
v___x_2300_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2293_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2311_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2301_);
v___x_2306_ = v___x_2217_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_del_object(v___x_2217_);
v_a_2312_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2300_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2300_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_one_2320_; lean_object* v_n_2321_; lean_object* v___x_2323_; 
v_one_2320_ = lean_unsigned_to_nat(1u);
v_n_2321_ = lean_nat_sub(v_n_2294_, v_one_2320_);
lean_dec(v_n_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 0);
lean_ctor_set(v___x_2296_, 0, v_n_2321_);
v___x_2323_ = v___x_2296_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_n_2321_);
v___x_2323_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set_tag(v___x_2209_, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2323_);
v___x_2325_ = v___x_2209_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2327_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_2198_, v___x_2325_, v___x_2326_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v_fvarId_2331_; lean_object* v_fvarId_2332_; lean_object* v___x_2333_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2330_ = lean_array_get_borrowed(v___x_2329_, v_params_2292_, v_zero_2298_);
v_fvarId_2331_ = lean_ctor_get(v___x_2330_, 0);
v_fvarId_2332_ = lean_ctor_get(v_a_2328_, 0);
lean_inc(v_fvarId_2332_);
lean_inc(v_fvarId_2331_);
v___x_2333_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2331_, v_fvarId_2332_, v_a_2184_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2334_; 
lean_dec_ref_known(v___x_2333_, 1);
lean_inc_ref(v_a_2188_);
v___x_2334_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2293_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2198_, v_params_2292_, v_a_2187_);
lean_dec_ref(v_params_2292_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2349_; 
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v___x_2336_, 0);
lean_dec(v_unused_2350_);
v___x_2338_ = v___x_2336_;
v_isShared_2339_ = v_isSharedCheck_2349_;
goto v_resetjp_2337_;
}
else
{
lean_dec(v___x_2336_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2349_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v_a_2335_);
lean_ctor_set(v___x_2233_, 0, v_a_2328_);
v___x_2341_ = v___x_2233_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2328_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_a_2335_);
v___x_2341_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2341_);
v___x_2343_ = v___x_2217_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2343_);
v___x_2345_ = v___x_2338_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
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
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_a_2335_);
lean_dec(v_a_2328_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2217_);
v_a_2351_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2336_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2336_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_a_2328_);
lean_dec_ref(v_params_2292_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2217_);
v_a_2359_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2334_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2334_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2328_);
lean_dec_ref(v_code_2293_);
lean_dec_ref(v_params_2292_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2217_);
v_a_2367_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2333_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2333_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_code_2293_);
lean_dec_ref(v_params_2292_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2217_);
v_a_2375_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2327_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2327_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
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
lean_object* v_code_2386_; lean_object* v___x_2387_; 
lean_del_object(v___x_2233_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
v_code_2386_ = lean_ctor_get(v_fst_2230_, 0);
lean_inc_ref(v_code_2386_);
lean_dec_ref_known(v_fst_2230_, 1);
lean_inc_ref(v_a_2188_);
v___x_2387_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2386_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2398_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2388_);
v___x_2393_ = v___x_2217_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_del_object(v___x_2217_);
v_a_2399_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2387_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2387_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_del_object(v___x_2233_);
lean_dec(v_fst_2230_);
lean_del_object(v___x_2217_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
v_a_2407_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2238_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2238_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2233_);
lean_dec(v_fst_2230_);
lean_del_object(v___x_2217_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
v_a_2415_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2237_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2237_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
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
lean_del_object(v___x_2217_);
lean_dec(v_val_2215_);
lean_dec(v___x_2213_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
lean_del_object(v___x_2205_);
lean_dec_ref(v_cases_2182_);
goto v___jp_2191_;
}
}
}
else
{
lean_dec(v___x_2214_);
lean_dec(v___x_2213_);
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
lean_del_object(v___x_2205_);
lean_dec_ref(v_cases_2182_);
goto v___jp_2191_;
}
}
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec(v_a_2203_);
lean_dec_ref(v_cases_2182_);
v___x_2428_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2428_);
v___x_2430_ = v___x_2205_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_cases_2182_);
v_a_2433_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2202_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2202_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v___x_2441_; 
lean_dec_ref(v_cases_2182_);
v___x_2441_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2198_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2442_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2441_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2441_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
v___jp_2191_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2459_, lean_object* v_i_2460_, lean_object* v_as_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = lean_array_get_size(v_as_2461_);
v___x_2471_ = lean_nat_dec_lt(v_i_2460_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_as_2461_);
return v___x_2472_;
}
else
{
lean_object* v_a_2473_; lean_object* v_a_2475_; 
v_a_2473_ = lean_array_fget_borrowed(v_as_2461_, v_i_2460_);
if (lean_obj_tag(v_a_2473_) == 0)
{
lean_object* v_ctorName_2486_; lean_object* v_params_2487_; lean_object* v_code_2488_; uint8_t v___x_2511_; uint8_t v_a_2513_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_ctorName_2486_ = lean_ctor_get(v_a_2473_, 0);
v_params_2487_ = lean_ctor_get(v_a_2473_, 1);
v_code_2488_ = lean_ctor_get(v_a_2473_, 2);
v___x_2511_ = 0;
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v_params_2487_);
v___x_2546_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
v_a_2513_ = v___x_2546_;
goto v___jp_2512_;
}
else
{
if (v___x_2546_ == 0)
{
v_a_2513_ = v___x_2546_;
goto v___jp_2512_;
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2545_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2487_, v___x_2547_, v___x_2548_, v___y_2468_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; uint8_t v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = lean_unbox(v_a_2550_);
lean_dec(v_a_2550_);
v_a_2513_ = v___x_2551_;
goto v___jp_2512_;
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2552_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2549_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2549_);
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
v___jp_2489_:
{
lean_object* v___x_2490_; 
lean_inc_ref(v_params_2487_);
lean_inc(v_ctorName_2486_);
lean_inc(v_fvarId_2459_);
v___x_2490_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2459_, v_ctorName_2486_, v_params_2487_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2492_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
lean_inc_ref(v___y_2467_);
lean_inc_ref(v_code_2488_);
v___x_2492_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2488_, v___y_2462_, v___y_2463_, v_a_2491_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v_a_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
lean_inc_ref(v_a_2473_);
v___x_2494_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2473_, v_a_2493_);
v_a_2475_ = v___x_2494_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2495_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2492_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2492_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2503_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2490_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2490_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
v___jp_2512_:
{
if (lean_obj_tag(v_code_2488_) == 6)
{
goto v___jp_2489_;
}
else
{
if (v_a_2513_ == 0)
{
goto v___jp_2489_;
}
else
{
lean_object* v___x_2514_; 
lean_inc_ref(v_code_2488_);
v___x_2514_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2511_, v_code_2488_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2511_, v_code_2488_, v___y_2466_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2517_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2463_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref_known(v___x_2517_, 1);
v___x_2518_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_a_2515_);
lean_inc_ref(v_a_2473_);
v___x_2519_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2473_, v___x_2518_);
v_a_2475_ = v___x_2519_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2520_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2517_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2517_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2528_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2516_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2516_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2536_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2514_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2514_);
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
}
}
}
else
{
lean_object* v_code_2560_; lean_object* v___x_2561_; 
v_code_2560_ = lean_ctor_get(v_a_2473_, 0);
lean_inc_ref(v___y_2467_);
lean_inc_ref(v_code_2560_);
v___x_2561_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2560_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
lean_inc_ref(v_a_2473_);
v___x_2563_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2473_, v_a_2562_);
v_a_2475_ = v___x_2563_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v_as_2461_);
lean_dec(v_i_2460_);
lean_dec(v_fvarId_2459_);
v_a_2564_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2561_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2561_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
v___jp_2474_:
{
size_t v___x_2476_; size_t v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = lean_ptr_addr(v_a_2473_);
v___x_2477_ = lean_ptr_addr(v_a_2475_);
v___x_2478_ = lean_usize_dec_eq(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_i_2460_, v___x_2479_);
v___x_2481_ = lean_array_fset(v_as_2461_, v_i_2460_, v_a_2475_);
lean_dec(v_i_2460_);
v_i_2460_ = v___x_2480_;
v_as_2461_ = v___x_2481_;
goto _start;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec_ref(v_a_2475_);
v___x_2483_ = lean_unsigned_to_nat(1u);
v___x_2484_ = lean_nat_add(v_i_2460_, v___x_2483_);
lean_dec(v_i_2460_);
v_i_2460_ = v___x_2484_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___y_2585_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___y_2592_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2619_; uint8_t v___y_2620_; lean_object* v_decl_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2670_; uint8_t v___y_2671_; lean_object* v_decl_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v_decl_2691_; lean_object* v_k_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_used_2963_; lean_object* v_binderRenaming_2964_; lean_object* v_funDeclInfoMap_2965_; uint8_t v_simplified_2966_; lean_object* v_visited_2967_; lean_object* v_inline_2968_; lean_object* v_inlineLocal_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v_i_3022_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v_i_3063_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; uint8_t v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v_decl_3095_; lean_object* v_fvarId_3096_; lean_object* v_type_3097_; lean_object* v_value_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; uint8_t v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v_fileName_3602_; lean_object* v_fileMap_3603_; lean_object* v_options_3604_; lean_object* v_currRecDepth_3605_; lean_object* v_maxRecDepth_3606_; lean_object* v_ref_3607_; lean_object* v_currNamespace_3608_; lean_object* v_openDecls_3609_; lean_object* v_initHeartbeats_3610_; lean_object* v_maxHeartbeats_3611_; lean_object* v_quotContext_3612_; lean_object* v_currMacroScope_3613_; uint8_t v_diag_3614_; lean_object* v_cancelTk_x3f_3615_; uint8_t v_suppressElabErrors_3616_; lean_object* v_inheritedTraceOptions_3617_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_fileName_3602_ = lean_ctor_get(v_a_2579_, 0);
v_fileMap_3603_ = lean_ctor_get(v_a_2579_, 1);
v_options_3604_ = lean_ctor_get(v_a_2579_, 2);
v_currRecDepth_3605_ = lean_ctor_get(v_a_2579_, 3);
v_maxRecDepth_3606_ = lean_ctor_get(v_a_2579_, 4);
v_ref_3607_ = lean_ctor_get(v_a_2579_, 5);
v_currNamespace_3608_ = lean_ctor_get(v_a_2579_, 6);
v_openDecls_3609_ = lean_ctor_get(v_a_2579_, 7);
v_initHeartbeats_3610_ = lean_ctor_get(v_a_2579_, 8);
v_maxHeartbeats_3611_ = lean_ctor_get(v_a_2579_, 9);
v_quotContext_3612_ = lean_ctor_get(v_a_2579_, 10);
v_currMacroScope_3613_ = lean_ctor_get(v_a_2579_, 11);
v_diag_3614_ = lean_ctor_get_uint8(v_a_2579_, sizeof(void*)*14);
v_cancelTk_x3f_3615_ = lean_ctor_get(v_a_2579_, 12);
v_suppressElabErrors_3616_ = lean_ctor_get_uint8(v_a_2579_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3617_ = lean_ctor_get(v_a_2579_, 13);
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = lean_nat_dec_eq(v_maxRecDepth_3606_, v___x_3647_);
if (v___x_3648_ == 0)
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_nat_dec_eq(v_currRecDepth_3605_, v_maxRecDepth_3606_);
if (v___x_3649_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3617_);
lean_inc(v_cancelTk_x3f_3615_);
lean_inc(v_currMacroScope_3613_);
lean_inc(v_quotContext_3612_);
lean_inc(v_maxHeartbeats_3611_);
lean_inc(v_initHeartbeats_3610_);
lean_inc(v_openDecls_3609_);
lean_inc(v_currNamespace_3608_);
lean_inc(v_ref_3607_);
lean_inc(v_maxRecDepth_3606_);
lean_inc(v_currRecDepth_3605_);
lean_inc_ref(v_options_3604_);
lean_inc_ref(v_fileMap_3603_);
lean_inc_ref(v_fileName_3602_);
lean_dec_ref(v_a_2579_);
goto v___jp_3618_;
}
else
{
lean_object* v___x_3650_; 
lean_dec_ref(v_code_2573_);
v___x_3650_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec_ref(v_a_2579_);
return v___x_3650_;
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3617_);
lean_inc(v_cancelTk_x3f_3615_);
lean_inc(v_currMacroScope_3613_);
lean_inc(v_quotContext_3612_);
lean_inc(v_maxHeartbeats_3611_);
lean_inc(v_initHeartbeats_3610_);
lean_inc(v_openDecls_3609_);
lean_inc(v_currNamespace_3608_);
lean_inc(v_ref_3607_);
lean_inc(v_maxRecDepth_3606_);
lean_inc(v_currRecDepth_3605_);
lean_inc_ref(v_options_3604_);
lean_inc_ref(v_fileMap_3603_);
lean_inc_ref(v_fileName_3602_);
lean_dec_ref(v_a_2579_);
goto v___jp_3618_;
}
v___jp_2582_:
{
if (v___y_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v_code_2573_);
v___x_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___y_2584_);
lean_ctor_set(v___x_2586_, 1, v___y_2583_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; 
lean_dec_ref(v___y_2584_);
lean_dec_ref(v___y_2583_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_code_2573_);
return v___x_2588_;
}
}
v___jp_2589_:
{
if (v___y_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec_ref(v_code_2573_);
v___x_2593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___y_2591_);
lean_ctor_set(v___x_2593_, 1, v___y_2590_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2590_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_code_2573_);
return v___x_2595_;
}
}
v___jp_2596_:
{
switch(lean_obj_tag(v_code_2573_))
{
case 1:
{
lean_object* v_decl_2599_; lean_object* v_k_2600_; size_t v___x_2601_; size_t v___x_2602_; uint8_t v___x_2603_; 
v_decl_2599_ = lean_ctor_get(v_code_2573_, 0);
v_k_2600_ = lean_ctor_get(v_code_2573_, 1);
v___x_2601_ = lean_ptr_addr(v_k_2600_);
v___x_2602_ = lean_ptr_addr(v___y_2597_);
v___x_2603_ = lean_usize_dec_eq(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
v___y_2583_ = v___y_2597_;
v___y_2584_ = v___y_2598_;
v___y_2585_ = v___x_2603_;
goto v___jp_2582_;
}
else
{
size_t v___x_2604_; size_t v___x_2605_; uint8_t v___x_2606_; 
v___x_2604_ = lean_ptr_addr(v_decl_2599_);
v___x_2605_ = lean_ptr_addr(v___y_2598_);
v___x_2606_ = lean_usize_dec_eq(v___x_2604_, v___x_2605_);
v___y_2583_ = v___y_2597_;
v___y_2584_ = v___y_2598_;
v___y_2585_ = v___x_2606_;
goto v___jp_2582_;
}
}
case 2:
{
lean_object* v_decl_2607_; lean_object* v_k_2608_; size_t v___x_2609_; size_t v___x_2610_; uint8_t v___x_2611_; 
v_decl_2607_ = lean_ctor_get(v_code_2573_, 0);
v_k_2608_ = lean_ctor_get(v_code_2573_, 1);
v___x_2609_ = lean_ptr_addr(v_k_2608_);
v___x_2610_ = lean_ptr_addr(v___y_2597_);
v___x_2611_ = lean_usize_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___x_2611_;
goto v___jp_2589_;
}
else
{
size_t v___x_2612_; size_t v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = lean_ptr_addr(v_decl_2607_);
v___x_2613_ = lean_ptr_addr(v___y_2598_);
v___x_2614_ = lean_usize_dec_eq(v___x_2612_, v___x_2613_);
v___y_2590_ = v___y_2597_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___x_2614_;
goto v___jp_2589_;
}
}
default: 
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_code_2573_);
v___x_2615_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2616_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
}
v___jp_2618_:
{
lean_object* v___x_2629_; 
lean_inc_ref(v___y_2627_);
v___x_2629_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2619_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v_fvarId_2631_; lean_object* v___x_2632_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v_fvarId_2631_ = lean_ctor_get(v_decl_2621_, 0);
v___x_2632_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2631_, v___y_2623_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = lean_unbox(v_a_2633_);
lean_dec(v_a_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_code_2573_);
v___x_2635_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2621_, v___y_2623_, v___y_2626_);
lean_dec_ref(v_decl_2621_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2643_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_a_2630_);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2630_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_a_2630_);
v_a_2644_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2635_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2635_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
if (v___y_2620_ == 0)
{
lean_dec_ref(v___y_2627_);
v___y_2597_ = v_a_2630_;
v___y_2598_ = v_decl_2621_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2652_; 
lean_inc_ref(v_decl_2621_);
v___x_2652_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec_ref(v___y_2627_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_dec_ref_known(v___x_2652_, 1);
v___y_2597_ = v_a_2630_;
v___y_2598_ = v_decl_2621_;
goto v___jp_2596_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2630_);
lean_dec_ref(v_decl_2621_);
lean_dec_ref(v_code_2573_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2630_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_decl_2621_);
lean_dec_ref(v_code_2573_);
v_a_2661_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2632_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2632_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_decl_2621_);
lean_dec_ref(v_code_2573_);
return v___x_2629_;
}
}
v___jp_2669_:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___y_2619_ = v___y_2670_;
v___y_2620_ = v___y_2671_;
v_decl_2621_ = v_a_2681_;
v___y_2622_ = v___y_2673_;
v___y_2623_ = v___y_2674_;
v___y_2624_ = v___y_2675_;
v___y_2625_ = v___y_2676_;
v___y_2626_ = v___y_2677_;
v___y_2627_ = v___y_2678_;
v___y_2628_ = v___y_2679_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2670_);
lean_dec_ref(v_code_2573_);
v_a_2682_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2680_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2680_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
v___jp_2690_:
{
lean_object* v_fvarId_2700_; lean_object* v_params_2701_; lean_object* v_type_2702_; lean_object* v___x_2703_; 
v_fvarId_2700_ = lean_ctor_get(v_decl_2691_, 0);
v_params_2701_ = lean_ctor_get(v_decl_2691_, 2);
v_type_2702_ = lean_ctor_get(v_decl_2691_, 3);
v___x_2703_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2700_, v___y_2694_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; uint8_t v___x_2705_; uint8_t v___x_2706_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = 0;
v___x_2706_ = lean_unbox(v_a_2704_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
v___x_2707_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2573_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
v___y_2670_ = v_k_2692_;
v___y_2671_ = v___x_2708_;
v_decl_2672_ = v_decl_2691_;
v___y_2673_ = v___y_2693_;
v___y_2674_ = v___y_2694_;
v___y_2675_ = v___y_2695_;
v___y_2676_ = v___y_2696_;
v___y_2677_ = v___y_2697_;
v___y_2678_ = v___y_2698_;
v___y_2679_ = v___y_2699_;
goto v___jp_2669_;
}
else
{
uint8_t v___x_2709_; 
lean_inc_ref(v_type_2702_);
v___x_2709_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2702_, v_params_2701_);
if (v___x_2709_ == 0)
{
uint8_t v___x_2710_; 
v___x_2710_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
v___y_2670_ = v_k_2692_;
v___y_2671_ = v___x_2710_;
v_decl_2672_ = v_decl_2691_;
v___y_2673_ = v___y_2693_;
v___y_2674_ = v___y_2694_;
v___y_2675_ = v___y_2695_;
v___y_2676_ = v___y_2696_;
v___y_2677_ = v___y_2697_;
v___y_2678_ = v___y_2698_;
v___y_2679_ = v___y_2699_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2711_; lean_object* v_subst_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = lean_st_ref_get(v___y_2694_);
v_subst_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc_ref(v_subst_2712_);
lean_dec(v___x_2711_);
v___x_2713_ = lean_unbox(v_a_2704_);
v___x_2714_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2705_, v___x_2713_, v_decl_2691_, v_subst_2712_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec_ref(v_subst_2712_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2715_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2694_);
if (lean_obj_tag(v___x_2718_) == 0)
{
uint8_t v___x_2719_; 
lean_dec_ref_known(v___x_2718_, 1);
v___x_2719_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
v___y_2670_ = v_k_2692_;
v___y_2671_ = v___x_2719_;
v_decl_2672_ = v_a_2717_;
v___y_2673_ = v___y_2693_;
v___y_2674_ = v___y_2694_;
v___y_2675_ = v___y_2695_;
v___y_2676_ = v___y_2696_;
v___y_2677_ = v___y_2697_;
v___y_2678_ = v___y_2698_;
v___y_2679_ = v___y_2699_;
goto v___jp_2669_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2717_);
lean_dec(v_a_2704_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_code_2573_);
v_a_2720_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2718_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_code_2573_);
v_a_2728_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2716_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2716_);
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
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_code_2573_);
v_a_2736_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2714_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2714_);
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
}
}
else
{
lean_object* v___x_2744_; lean_object* v_subst_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2744_ = lean_st_ref_get(v___y_2694_);
v_subst_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_ref(v_subst_2745_);
lean_dec(v___x_2744_);
v___x_2746_ = 0;
v___x_2747_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2705_, v___x_2746_, v_decl_2691_, v_subst_2745_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec_ref(v_subst_2745_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; uint8_t v___x_2749_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
v___y_2619_ = v_k_2692_;
v___y_2620_ = v___x_2749_;
v_decl_2621_ = v_a_2748_;
v___y_2622_ = v___y_2693_;
v___y_2623_ = v___y_2694_;
v___y_2624_ = v___y_2695_;
v___y_2625_ = v___y_2696_;
v___y_2626_ = v___y_2697_;
v___y_2627_ = v___y_2698_;
v___y_2628_ = v___y_2699_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_code_2573_);
v_a_2750_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2747_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2747_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_decl_2691_);
lean_dec_ref(v_code_2573_);
v_a_2758_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2703_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2703_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
v___jp_2766_:
{
if (v___y_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec_ref(v_code_2573_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2768_);
lean_ctor_set(v___x_2770_, 1, v___y_2767_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
else
{
lean_object* v___x_2772_; 
lean_dec_ref(v___y_2768_);
lean_dec_ref(v___y_2767_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_code_2573_);
return v___x_2772_;
}
}
v___jp_2773_:
{
lean_object* v___x_2784_; 
lean_inc_ref(v___y_2782_);
v___x_2784_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2782_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
if (lean_obj_tag(v_a_2785_) == 1)
{
lean_object* v_val_2786_; lean_object* v___x_2787_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_val_2786_ = lean_ctor_get(v_a_2785_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v_a_2785_, 1);
v___x_2787_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2783_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_inc_ref(v___y_2778_);
v___x_2788_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2781_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2786_, v_a_2789_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
lean_dec_ref(v___y_2778_);
lean_dec(v_val_2786_);
return v___x_2790_;
}
else
{
lean_dec(v_val_2786_);
lean_dec_ref(v___y_2778_);
return v___x_2788_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_val_2786_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
v_a_2791_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2787_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2799_; 
lean_dec(v_a_2785_);
lean_inc_ref(v___y_2782_);
v___x_2799_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2782_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
if (lean_obj_tag(v_a_2800_) == 1)
{
lean_object* v_val_2801_; lean_object* v___x_2802_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_val_2801_ = lean_ctor_get(v_a_2800_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_a_2800_, 1);
v___x_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2802_, 0, v_val_2801_);
lean_ctor_set(v___x_2802_, 1, v___y_2781_);
v_code_2573_ = v___x_2802_;
v_a_2574_ = v___y_2780_;
v_a_2575_ = v___y_2783_;
v_a_2576_ = v___y_2779_;
v_a_2577_ = v___y_2776_;
v_a_2578_ = v___y_2777_;
v_a_2579_ = v___y_2778_;
v_a_2580_ = v___y_2775_;
goto _start;
}
else
{
lean_object* v_fvarId_2804_; lean_object* v_value_2805_; lean_object* v___x_2806_; 
lean_dec(v_a_2800_);
v_fvarId_2804_ = lean_ctor_get(v___y_2782_, 0);
v_value_2805_ = lean_ctor_get(v___y_2782_, 3);
v___x_2806_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2805_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
if (lean_obj_tag(v_a_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v___x_2809_; 
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_val_2808_ = lean_ctor_get(v_a_2807_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_a_2807_, 1);
lean_inc(v_fvarId_2804_);
v___x_2809_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2804_, v_val_2808_, v___y_2783_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2782_, v___y_2783_, v___y_2777_);
lean_dec_ref(v___y_2782_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_dec_ref_known(v___x_2810_, 1);
v_code_2573_ = v___y_2781_;
v_a_2574_ = v___y_2780_;
v_a_2575_ = v___y_2783_;
v_a_2576_ = v___y_2779_;
v_a_2577_ = v___y_2776_;
v_a_2578_ = v___y_2777_;
v_a_2579_ = v___y_2778_;
v_a_2580_ = v___y_2775_;
goto _start;
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
v_a_2812_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2810_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2810_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
v_a_2820_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2809_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2809_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v___x_2828_; 
lean_dec(v_a_2807_);
lean_inc_ref(v___y_2781_);
lean_inc_ref(v___y_2782_);
v___x_2828_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2782_, v___y_2781_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
if (lean_obj_tag(v_a_2829_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_val_2830_ = lean_ctor_get(v_a_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v_a_2829_, 1);
v___x_2831_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2782_, v___y_2783_, v___y_2777_);
lean_dec_ref(v___y_2782_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2839_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v_val_2830_);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_val_2830_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_val_2830_);
v_a_2840_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2831_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2831_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v___x_2848_; 
lean_dec(v_a_2829_);
lean_inc(v_value_2805_);
v___x_2848_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2805_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
if (lean_obj_tag(v_a_2849_) == 1)
{
lean_object* v_val_2850_; lean_object* v_fst_2851_; lean_object* v_snd_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_val_2850_ = lean_ctor_get(v_a_2849_, 0);
lean_inc(v_val_2850_);
lean_dec_ref_known(v_a_2849_, 1);
v_fst_2851_ = lean_ctor_get(v_val_2850_, 0);
lean_inc(v_fst_2851_);
v_snd_2852_ = lean_ctor_get(v_val_2850_, 1);
lean_inc(v_snd_2852_);
lean_dec(v_val_2850_);
lean_inc(v_fvarId_2804_);
v___x_2853_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2804_, v_snd_2852_, v___y_2783_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref_known(v___x_2853_, 1);
v___x_2854_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2782_, v___y_2783_, v___y_2777_);
lean_dec_ref(v___y_2782_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref_known(v___x_2854_, 1);
lean_inc_ref(v___y_2778_);
v___x_2855_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2781_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2851_, v_a_2856_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
lean_dec_ref(v___y_2778_);
lean_dec(v_fst_2851_);
return v___x_2857_;
}
else
{
lean_dec(v_fst_2851_);
lean_dec_ref(v___y_2778_);
return v___x_2855_;
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_fst_2851_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
v_a_2858_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2854_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2854_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_fst_2851_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
v_a_2866_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2853_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2853_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_a_2849_);
lean_inc_ref(v___y_2778_);
lean_inc_ref(v___y_2781_);
v___x_2874_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2781_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2804_, v___y_2783_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; uint8_t v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = lean_unbox(v_a_2877_);
lean_dec(v_a_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v___x_2879_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2782_, v___y_2783_, v___y_2777_);
lean_dec_ref(v___y_2782_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2887_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v_a_2875_);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2875_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_a_2875_);
v_a_2888_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2879_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2879_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v___x_2896_; 
lean_inc_ref(v___y_2782_);
v___x_2896_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2782_, v___y_2780_, v___y_2783_, v___y_2779_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2775_);
lean_dec_ref(v___y_2778_);
if (lean_obj_tag(v___x_2896_) == 0)
{
size_t v___x_2897_; size_t v___x_2898_; uint8_t v___x_2899_; 
lean_dec_ref_known(v___x_2896_, 1);
v___x_2897_ = lean_ptr_addr(v___y_2781_);
lean_dec_ref(v___y_2781_);
v___x_2898_ = lean_ptr_addr(v_a_2875_);
v___x_2899_ = lean_usize_dec_eq(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_dec_ref(v___y_2774_);
v___y_2767_ = v_a_2875_;
v___y_2768_ = v___y_2782_;
v___y_2769_ = v___x_2899_;
goto v___jp_2766_;
}
else
{
size_t v___x_2900_; size_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2900_ = lean_ptr_addr(v___y_2774_);
lean_dec_ref(v___y_2774_);
v___x_2901_ = lean_ptr_addr(v___y_2782_);
v___x_2902_ = lean_usize_dec_eq(v___x_2900_, v___x_2901_);
v___y_2767_ = v_a_2875_;
v___y_2768_ = v___y_2782_;
v___y_2769_ = v___x_2902_;
goto v___jp_2766_;
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2875_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2903_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2896_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2896_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2875_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2911_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2876_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2876_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
return v___x_2874_;
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2919_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2848_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2848_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2927_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2828_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2828_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2935_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2806_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2806_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2943_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2799_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2799_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2774_);
lean_dec_ref(v_code_2573_);
v_a_2951_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2784_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2784_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
v___jp_2959_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2977_, 0, v___y_2976_);
lean_ctor_set(v___x_2977_, 1, v_used_2963_);
lean_ctor_set(v___x_2977_, 2, v_binderRenaming_2964_);
lean_ctor_set(v___x_2977_, 3, v_funDeclInfoMap_2965_);
lean_ctor_set(v___x_2977_, 4, v_visited_2967_);
lean_ctor_set(v___x_2977_, 5, v_inline_2968_);
lean_ctor_set(v___x_2977_, 6, v_inlineLocal_2969_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*7, v_simplified_2966_);
v___x_2978_ = lean_st_ref_put(v___y_2975_, v___x_2977_);
v___x_2979_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2974_, v___y_2975_, v___y_2962_);
lean_dec_ref(v___y_2974_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_dec_ref_known(v___x_2979_, 1);
v_code_2573_ = v___y_2972_;
v_a_2574_ = v___y_2971_;
v_a_2575_ = v___y_2975_;
v_a_2576_ = v___y_2970_;
v_a_2577_ = v___y_2961_;
v_a_2578_ = v___y_2962_;
v_a_2579_ = v___y_2973_;
v_a_2580_ = v___y_2960_;
goto _start;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___y_2972_);
v_a_2981_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
v___jp_2989_:
{
lean_object* v_used_3001_; lean_object* v_binderRenaming_3002_; lean_object* v_funDeclInfoMap_3003_; uint8_t v_simplified_3004_; lean_object* v_visited_3005_; lean_object* v_inline_3006_; lean_object* v_inlineLocal_3007_; 
v_used_3001_ = lean_ctor_get(v___y_2993_, 1);
lean_inc(v_used_3001_);
v_binderRenaming_3002_ = lean_ctor_get(v___y_2993_, 2);
lean_inc(v_binderRenaming_3002_);
v_funDeclInfoMap_3003_ = lean_ctor_get(v___y_2993_, 3);
lean_inc_ref(v_funDeclInfoMap_3003_);
v_simplified_3004_ = lean_ctor_get_uint8(v___y_2993_, sizeof(void*)*7);
v_visited_3005_ = lean_ctor_get(v___y_2993_, 4);
lean_inc(v_visited_3005_);
v_inline_3006_ = lean_ctor_get(v___y_2993_, 5);
lean_inc(v_inline_3006_);
v_inlineLocal_3007_ = lean_ctor_get(v___y_2993_, 6);
lean_inc(v_inlineLocal_3007_);
lean_dec_ref(v___y_2993_);
v___y_2960_ = v___y_2990_;
v___y_2961_ = v___y_2991_;
v___y_2962_ = v___y_2992_;
v_used_2963_ = v_used_3001_;
v_binderRenaming_2964_ = v_binderRenaming_3002_;
v_funDeclInfoMap_2965_ = v_funDeclInfoMap_3003_;
v_simplified_2966_ = v_simplified_3004_;
v_visited_2967_ = v_visited_3005_;
v_inline_2968_ = v_inline_3006_;
v_inlineLocal_2969_ = v_inlineLocal_3007_;
v___y_2970_ = v___y_2994_;
v___y_2971_ = v___y_2995_;
v___y_2972_ = v___y_2996_;
v___y_2973_ = v___y_2997_;
v___y_2974_ = v___y_2998_;
v___y_2975_ = v___y_2999_;
v___y_2976_ = v___y_3000_;
goto v___jp_2959_;
}
v___jp_3008_:
{
lean_object* v_size_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_size_3023_ = lean_ctor_get(v___y_3013_, 0);
v___x_3024_ = lean_unsigned_to_nat(1u);
v___x_3025_ = lean_nat_add(v_size_3023_, v___x_3024_);
v___x_3026_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3013_, v___x_3025_, v_i_3022_, v___y_3015_, v___y_3021_);
lean_dec(v_i_3022_);
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3017_;
v___y_2993_ = v___y_3018_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___y_3011_;
v___y_2996_ = v___y_3012_;
v___y_2997_ = v___y_3019_;
v___y_2998_ = v___y_3020_;
v___y_2999_ = v___y_3014_;
v___y_3000_ = v___x_3026_;
goto v___jp_2989_;
}
v___jp_3027_:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___y_3040_, v___y_3033_);
switch(lean_obj_tag(v___x_3041_))
{
case 0:
{
lean_object* v_index_3042_; lean_object* v_size_3043_; lean_object* v___x_3044_; 
v_index_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_index_3042_);
lean_dec_ref_known(v___x_3041_, 3);
v_size_3043_ = lean_ctor_get(v___y_3040_, 0);
lean_inc(v_size_3043_);
v___x_3044_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3040_, v_size_3043_, v_index_3042_, v___y_3033_, v___y_3039_);
lean_dec(v_index_3042_);
v___y_2990_ = v___y_3034_;
v___y_2991_ = v___y_3028_;
v___y_2992_ = v___y_3035_;
v___y_2993_ = v___y_3036_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3037_;
v___y_2998_ = v___y_3038_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___x_3044_;
goto v___jp_2989_;
}
case 1:
{
lean_object* v_index_3045_; 
v_index_3045_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_index_3045_);
lean_dec_ref_known(v___x_3041_, 1);
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3029_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___y_3040_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v_i_3022_ = v_index_3045_;
goto v___jp_3008_;
}
default: 
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3040_, v___x_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_index_3048_; 
v_index_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_index_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3029_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___y_3040_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3037_;
v___y_3020_ = v___y_3038_;
v___y_3021_ = v___y_3039_;
v_i_3022_ = v_index_3048_;
goto v___jp_3008_;
}
else
{
lean_dec(v___y_3039_);
lean_dec(v___y_3033_);
v___y_2990_ = v___y_3034_;
v___y_2991_ = v___y_3028_;
v___y_2992_ = v___y_3035_;
v___y_2993_ = v___y_3036_;
v___y_2994_ = v___y_3029_;
v___y_2995_ = v___y_3030_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3037_;
v___y_2998_ = v___y_3038_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3040_;
goto v___jp_2989_;
}
}
}
}
v___jp_3049_:
{
lean_object* v_size_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_size_3064_ = lean_ctor_get(v___y_3050_, 0);
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = lean_nat_add(v_size_3064_, v___x_3065_);
v___x_3067_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3050_, v___x_3066_, v_i_3063_, v___y_3056_, v___y_3062_);
lean_dec(v_i_3063_);
v___y_2990_ = v___y_3057_;
v___y_2991_ = v___y_3051_;
v___y_2992_ = v___y_3058_;
v___y_2993_ = v___y_3059_;
v___y_2994_ = v___y_3052_;
v___y_2995_ = v___y_3053_;
v___y_2996_ = v___y_3054_;
v___y_2997_ = v___y_3060_;
v___y_2998_ = v___y_3061_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___x_3067_;
goto v___jp_2989_;
}
v___jp_3068_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v___y_3077_);
lean_dec_ref(v___y_3077_);
v___x_3083_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v___x_3082_, v___y_3074_);
switch(lean_obj_tag(v___x_3083_))
{
case 0:
{
lean_object* v_index_3084_; lean_object* v_size_3085_; lean_object* v___x_3086_; 
v_index_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_index_3084_);
lean_dec_ref_known(v___x_3083_, 3);
v_size_3085_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_size_3085_);
v___x_3086_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3082_, v_size_3085_, v_index_3084_, v___y_3074_, v___y_3081_);
lean_dec(v_index_3084_);
v___y_2990_ = v___y_3075_;
v___y_2991_ = v___y_3069_;
v___y_2992_ = v___y_3076_;
v___y_2993_ = v___y_3078_;
v___y_2994_ = v___y_3070_;
v___y_2995_ = v___y_3071_;
v___y_2996_ = v___y_3072_;
v___y_2997_ = v___y_3079_;
v___y_2998_ = v___y_3080_;
v___y_2999_ = v___y_3073_;
v___y_3000_ = v___x_3086_;
goto v___jp_2989_;
}
case 1:
{
lean_object* v_index_3087_; 
v_index_3087_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_index_3087_);
lean_dec_ref_known(v___x_3083_, 1);
v___y_3050_ = v___x_3082_;
v___y_3051_ = v___y_3069_;
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3073_;
v___y_3056_ = v___y_3074_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3081_;
v_i_3063_ = v_index_3087_;
goto v___jp_3049_;
}
default: 
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3082_, v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_index_3090_; 
v_index_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_index_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v___y_3050_ = v___x_3082_;
v___y_3051_ = v___y_3069_;
v___y_3052_ = v___y_3070_;
v___y_3053_ = v___y_3071_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3073_;
v___y_3056_ = v___y_3074_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3078_;
v___y_3060_ = v___y_3079_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3081_;
v_i_3063_ = v_index_3090_;
goto v___jp_3049_;
}
else
{
lean_dec(v___y_3081_);
lean_dec(v___y_3074_);
v___y_2990_ = v___y_3075_;
v___y_2991_ = v___y_3069_;
v___y_2992_ = v___y_3076_;
v___y_2993_ = v___y_3078_;
v___y_2994_ = v___y_3070_;
v___y_2995_ = v___y_3071_;
v___y_2996_ = v___y_3072_;
v___y_2997_ = v___y_3079_;
v___y_2998_ = v___y_3080_;
v___y_2999_ = v___y_3073_;
v___y_3000_ = v___x_3082_;
goto v___jp_2989_;
}
}
}
}
v___jp_3091_:
{
uint8_t v___x_3106_; 
v___x_3106_ = l_Lean_Expr_isErased(v_type_3097_);
lean_dec_ref(v_type_3097_);
if (v___x_3106_ == 0)
{
lean_dec(v_value_3098_);
lean_dec(v_fvarId_3096_);
v___y_2774_ = v___y_3094_;
v___y_2775_ = v___y_3105_;
v___y_2776_ = v___y_3102_;
v___y_2777_ = v___y_3103_;
v___y_2778_ = v___y_3104_;
v___y_2779_ = v___y_3101_;
v___y_2780_ = v___y_3099_;
v___y_2781_ = v___y_3093_;
v___y_2782_ = v_decl_3095_;
v___y_2783_ = v___y_3100_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = lean_box(1);
v___x_3108_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_3092_, v_value_3098_, v___x_3107_);
lean_dec(v_value_3098_);
if (v___x_3108_ == 0)
{
if (v___x_3106_ == 0)
{
lean_dec(v_fvarId_3096_);
v___y_2774_ = v___y_3094_;
v___y_2775_ = v___y_3105_;
v___y_2776_ = v___y_3102_;
v___y_2777_ = v___y_3103_;
v___y_2778_ = v___y_3104_;
v___y_2779_ = v___y_3101_;
v___y_2780_ = v___y_3099_;
v___y_2781_ = v___y_3093_;
v___y_2782_ = v_decl_3095_;
v___y_2783_ = v___y_3100_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_3109_; lean_object* v_subst_3110_; lean_object* v_used_3111_; lean_object* v_binderRenaming_3112_; lean_object* v_funDeclInfoMap_3113_; uint8_t v_simplified_3114_; lean_object* v_visited_3115_; lean_object* v_inline_3116_; lean_object* v_inlineLocal_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref(v___y_3094_);
lean_dec_ref(v_code_2573_);
v___x_3109_ = lean_st_ref_take(v___y_3100_);
v_subst_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc_ref(v_subst_3110_);
v_used_3111_ = lean_ctor_get(v___x_3109_, 1);
lean_inc(v_used_3111_);
v_binderRenaming_3112_ = lean_ctor_get(v___x_3109_, 2);
lean_inc(v_binderRenaming_3112_);
v_funDeclInfoMap_3113_ = lean_ctor_get(v___x_3109_, 3);
lean_inc_ref(v_funDeclInfoMap_3113_);
v_simplified_3114_ = lean_ctor_get_uint8(v___x_3109_, sizeof(void*)*7);
v_visited_3115_ = lean_ctor_get(v___x_3109_, 4);
lean_inc(v_visited_3115_);
v_inline_3116_ = lean_ctor_get(v___x_3109_, 5);
lean_inc(v_inline_3116_);
v_inlineLocal_3117_ = lean_ctor_get(v___x_3109_, 6);
lean_inc(v_inlineLocal_3117_);
v___x_3118_ = lean_box(0);
v___x_3119_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_3110_, v_fvarId_3096_);
switch(lean_obj_tag(v___x_3119_))
{
case 0:
{
lean_object* v_index_3120_; lean_object* v_size_3121_; lean_object* v___x_3122_; 
lean_dec(v___x_3109_);
v_index_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_index_3120_);
lean_dec_ref_known(v___x_3119_, 3);
v_size_3121_ = lean_ctor_get(v_subst_3110_, 0);
lean_inc(v_size_3121_);
v___x_3122_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_3110_, v_size_3121_, v_index_3120_, v_fvarId_3096_, v___x_3118_);
lean_dec(v_index_3120_);
v___y_2960_ = v___y_3105_;
v___y_2961_ = v___y_3102_;
v___y_2962_ = v___y_3103_;
v_used_2963_ = v_used_3111_;
v_binderRenaming_2964_ = v_binderRenaming_3112_;
v_funDeclInfoMap_2965_ = v_funDeclInfoMap_3113_;
v_simplified_2966_ = v_simplified_3114_;
v_visited_2967_ = v_visited_3115_;
v_inline_2968_ = v_inline_3116_;
v_inlineLocal_2969_ = v_inlineLocal_3117_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3099_;
v___y_2972_ = v___y_3093_;
v___y_2973_ = v___y_3104_;
v___y_2974_ = v_decl_3095_;
v___y_2975_ = v___y_3100_;
v___y_2976_ = v___x_3122_;
goto v___jp_2959_;
}
case 1:
{
lean_object* v_index_3123_; lean_object* v_size_3124_; lean_object* v_keyArray_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_index_3123_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_index_3123_);
lean_dec_ref_known(v___x_3119_, 1);
v_size_3124_ = lean_ctor_get(v_subst_3110_, 0);
v_keyArray_3125_ = lean_ctor_get(v_subst_3110_, 1);
v___x_3126_ = lean_unsigned_to_nat(1u);
v___x_3127_ = lean_nat_add(v_size_3124_, v___x_3126_);
v___x_3128_ = lean_array_get_size(v_keyArray_3125_);
v___x_3129_ = lean_nat_dec_lt(v___x_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec(v___x_3127_);
lean_dec(v_index_3123_);
lean_dec(v_inlineLocal_3117_);
lean_dec(v_inline_3116_);
lean_dec(v_visited_3115_);
lean_dec_ref(v_funDeclInfoMap_3113_);
lean_dec(v_binderRenaming_3112_);
lean_dec(v_used_3111_);
v___y_3069_ = v___y_3102_;
v___y_3070_ = v___y_3101_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_fvarId_3096_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3103_;
v___y_3077_ = v_subst_3110_;
v___y_3078_ = v___x_3109_;
v___y_3079_ = v___y_3104_;
v___y_3080_ = v_decl_3095_;
v___y_3081_ = v___x_3118_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3130_ = lean_unsigned_to_nat(4u);
v___x_3131_ = lean_nat_mul(v___x_3127_, v___x_3130_);
v___x_3132_ = lean_unsigned_to_nat(3u);
v___x_3133_ = lean_nat_mul(v___x_3128_, v___x_3132_);
v___x_3134_ = lean_nat_dec_le(v___x_3131_, v___x_3133_);
lean_dec(v___x_3133_);
lean_dec(v___x_3131_);
if (v___x_3134_ == 0)
{
lean_dec(v___x_3127_);
lean_dec(v_index_3123_);
lean_dec(v_inlineLocal_3117_);
lean_dec(v_inline_3116_);
lean_dec(v_visited_3115_);
lean_dec_ref(v_funDeclInfoMap_3113_);
lean_dec(v_binderRenaming_3112_);
lean_dec(v_used_3111_);
v___y_3069_ = v___y_3102_;
v___y_3070_ = v___y_3101_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_fvarId_3096_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3103_;
v___y_3077_ = v_subst_3110_;
v___y_3078_ = v___x_3109_;
v___y_3079_ = v___y_3104_;
v___y_3080_ = v_decl_3095_;
v___y_3081_ = v___x_3118_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3135_; 
lean_dec(v___x_3109_);
v___x_3135_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_3110_, v___x_3127_, v_index_3123_, v_fvarId_3096_, v___x_3118_);
lean_dec(v_index_3123_);
v___y_2960_ = v___y_3105_;
v___y_2961_ = v___y_3102_;
v___y_2962_ = v___y_3103_;
v_used_2963_ = v_used_3111_;
v_binderRenaming_2964_ = v_binderRenaming_3112_;
v_funDeclInfoMap_2965_ = v_funDeclInfoMap_3113_;
v_simplified_2966_ = v_simplified_3114_;
v_visited_2967_ = v_visited_3115_;
v_inline_2968_ = v_inline_3116_;
v_inlineLocal_2969_ = v_inlineLocal_3117_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3099_;
v___y_2972_ = v___y_3093_;
v___y_2973_ = v___y_3104_;
v___y_2974_ = v_decl_3095_;
v___y_2975_ = v___y_3100_;
v___y_2976_ = v___x_3135_;
goto v___jp_2959_;
}
}
}
default: 
{
lean_object* v_size_3136_; lean_object* v_keyArray_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
lean_dec(v_inlineLocal_3117_);
lean_dec(v_inline_3116_);
lean_dec(v_visited_3115_);
lean_dec_ref(v_funDeclInfoMap_3113_);
lean_dec(v_binderRenaming_3112_);
lean_dec(v_used_3111_);
v_size_3136_ = lean_ctor_get(v_subst_3110_, 0);
v_keyArray_3137_ = lean_ctor_get(v_subst_3110_, 1);
v___x_3138_ = lean_unsigned_to_nat(1u);
v___x_3139_ = lean_nat_add(v_size_3136_, v___x_3138_);
v___x_3140_ = lean_array_get_size(v_keyArray_3137_);
v___x_3141_ = lean_nat_dec_lt(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_dec(v___x_3139_);
v___x_3142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_subst_3110_);
lean_dec_ref(v_subst_3110_);
v___y_3028_ = v___y_3102_;
v___y_3029_ = v___y_3101_;
v___y_3030_ = v___y_3099_;
v___y_3031_ = v___y_3093_;
v___y_3032_ = v___y_3100_;
v___y_3033_ = v_fvarId_3096_;
v___y_3034_ = v___y_3105_;
v___y_3035_ = v___y_3103_;
v___y_3036_ = v___x_3109_;
v___y_3037_ = v___y_3104_;
v___y_3038_ = v_decl_3095_;
v___y_3039_ = v___x_3118_;
v___y_3040_ = v___x_3142_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3143_ = lean_unsigned_to_nat(4u);
v___x_3144_ = lean_nat_mul(v___x_3139_, v___x_3143_);
lean_dec(v___x_3139_);
v___x_3145_ = lean_unsigned_to_nat(3u);
v___x_3146_ = lean_nat_mul(v___x_3140_, v___x_3145_);
v___x_3147_ = lean_nat_dec_le(v___x_3144_, v___x_3146_);
lean_dec(v___x_3146_);
lean_dec(v___x_3144_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_subst_3110_);
lean_dec_ref(v_subst_3110_);
v___y_3028_ = v___y_3102_;
v___y_3029_ = v___y_3101_;
v___y_3030_ = v___y_3099_;
v___y_3031_ = v___y_3093_;
v___y_3032_ = v___y_3100_;
v___y_3033_ = v_fvarId_3096_;
v___y_3034_ = v___y_3105_;
v___y_3035_ = v___y_3103_;
v___y_3036_ = v___x_3109_;
v___y_3037_ = v___y_3104_;
v___y_3038_ = v_decl_3095_;
v___y_3039_ = v___x_3118_;
v___y_3040_ = v___x_3148_;
goto v___jp_3027_;
}
else
{
v___y_3028_ = v___y_3102_;
v___y_3029_ = v___y_3101_;
v___y_3030_ = v___y_3099_;
v___y_3031_ = v___y_3093_;
v___y_3032_ = v___y_3100_;
v___y_3033_ = v_fvarId_3096_;
v___y_3034_ = v___y_3105_;
v___y_3035_ = v___y_3103_;
v___y_3036_ = v___x_3109_;
v___y_3037_ = v___y_3104_;
v___y_3038_ = v_decl_3095_;
v___y_3039_ = v___x_3118_;
v___y_3040_ = v_subst_3110_;
goto v___jp_3027_;
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_3096_);
v___y_2774_ = v___y_3094_;
v___y_2775_ = v___y_3105_;
v___y_2776_ = v___y_3102_;
v___y_2777_ = v___y_3103_;
v___y_2778_ = v___y_3104_;
v___y_2779_ = v___y_3101_;
v___y_2780_ = v___y_3099_;
v___y_2781_ = v___y_3093_;
v___y_2782_ = v_decl_3095_;
v___y_2783_ = v___y_3100_;
goto v___jp_2773_;
}
}
}
v___jp_3149_:
{
lean_object* v_fvarId_3161_; lean_object* v_type_3162_; lean_object* v_value_3163_; lean_object* v___x_3164_; 
v_fvarId_3161_ = lean_ctor_get(v___y_3152_, 0);
v_type_3162_ = lean_ctor_get(v___y_3152_, 2);
v_value_3163_ = lean_ctor_get(v___y_3152_, 3);
lean_inc(v_value_3163_);
v___x_3164_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_3163_, v___y_3154_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
if (lean_obj_tag(v_a_3165_) == 1)
{
lean_object* v_val_3166_; lean_object* v___x_3167_; 
v_val_3166_ = lean_ctor_get(v_a_3165_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v_a_3165_, 1);
v___x_3167_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3155_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref_known(v___x_3167_, 1);
v___x_3168_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_3150_, v___y_3152_, v_val_3166_, v___y_3158_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v_fvarId_3170_; lean_object* v_type_3171_; lean_object* v_value_3172_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v_fvarId_3170_ = lean_ctor_get(v_a_3169_, 0);
lean_inc(v_fvarId_3170_);
v_type_3171_ = lean_ctor_get(v_a_3169_, 2);
lean_inc_ref(v_type_3171_);
v_value_3172_ = lean_ctor_get(v_a_3169_, 3);
lean_inc(v_value_3172_);
v___y_3092_ = v___y_3150_;
v___y_3093_ = v___y_3151_;
v___y_3094_ = v___y_3153_;
v_decl_3095_ = v_a_3169_;
v_fvarId_3096_ = v_fvarId_3170_;
v_type_3097_ = v_type_3171_;
v_value_3098_ = v_value_3172_;
v___y_3099_ = v___y_3154_;
v___y_3100_ = v___y_3155_;
v___y_3101_ = v___y_3156_;
v___y_3102_ = v___y_3157_;
v___y_3103_ = v___y_3158_;
v___y_3104_ = v___y_3159_;
v___y_3105_ = v___y_3160_;
goto v___jp_3091_;
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v_code_2573_);
v_a_3173_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3168_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3168_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_val_3166_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v_code_2573_);
v_a_3181_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3167_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3167_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_inc(v_value_3163_);
lean_inc_ref(v_type_3162_);
lean_inc(v_fvarId_3161_);
lean_dec(v_a_3165_);
v___y_3092_ = v___y_3150_;
v___y_3093_ = v___y_3151_;
v___y_3094_ = v___y_3153_;
v_decl_3095_ = v___y_3152_;
v_fvarId_3096_ = v_fvarId_3161_;
v_type_3097_ = v_type_3162_;
v_value_3098_ = v_value_3163_;
v___y_3099_ = v___y_3154_;
v___y_3100_ = v___y_3155_;
v___y_3101_ = v___y_3156_;
v___y_3102_ = v___y_3157_;
v___y_3103_ = v___y_3158_;
v___y_3104_ = v___y_3159_;
v___y_3105_ = v___y_3160_;
goto v___jp_3091_;
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v_code_2573_);
v_a_3189_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3164_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3164_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
v___jp_3197_:
{
if (v___y_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_dec_ref(v_code_2573_);
v___x_3201_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3198_);
lean_ctor_set(v___x_3201_, 1, v___y_3199_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
else
{
lean_object* v___x_3203_; 
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_code_2573_);
return v___x_3203_;
}
}
v___jp_3204_:
{
uint8_t v___x_3209_; 
v___x_3209_ = l_Lean_instBEqFVarId_beq(v___y_3207_, v___y_3205_);
lean_dec(v___y_3207_);
if (v___x_3209_ == 0)
{
lean_dec_ref(v___y_3208_);
v___y_3198_ = v___y_3205_;
v___y_3199_ = v___y_3206_;
v___y_3200_ = v___x_3209_;
goto v___jp_3197_;
}
else
{
size_t v___x_3210_; size_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = lean_ptr_addr(v___y_3208_);
lean_dec_ref(v___y_3208_);
v___x_3211_ = lean_ptr_addr(v___y_3206_);
v___x_3212_ = lean_usize_dec_eq(v___x_3210_, v___x_3211_);
v___y_3198_ = v___y_3205_;
v___y_3199_ = v___y_3206_;
v___y_3200_ = v___x_3212_;
goto v___jp_3197_;
}
}
v___jp_3213_:
{
if (lean_obj_tag(v___y_3218_) == 0)
{
lean_dec_ref_known(v___y_3218_, 1);
v___y_3205_ = v___y_3214_;
v___y_3206_ = v___y_3215_;
v___y_3207_ = v___y_3216_;
v___y_3208_ = v___y_3217_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v_code_2573_);
v_a_3219_ = lean_ctor_get(v___y_3218_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___y_3218_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___y_3218_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___y_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3228_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3238_; 
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3230_, 0);
lean_dec(v_unused_3239_);
v___x_3232_ = v___x_3230_;
v_isShared_3233_ = v_isSharedCheck_3238_;
goto v_resetjp_3231_;
}
else
{
lean_dec(v___x_3230_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3238_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___y_3229_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3234_);
v___x_3236_ = v___x_3232_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___y_3229_);
v_a_3240_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3230_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3230_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
v___jp_3248_:
{
if (lean_obj_tag(v___y_3251_) == 0)
{
lean_dec_ref_known(v___y_3251_, 1);
v___y_3228_ = v___y_3249_;
v___y_3229_ = v___y_3250_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3250_);
v_a_3252_ = lean_ctor_get(v___y_3251_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___y_3251_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___y_3251_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___y_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
v___jp_3260_:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_nat_dec_lt(v___y_3261_, v___y_3267_);
lean_dec(v___y_3261_);
if (v___x_3270_ == 0)
{
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
v___y_3228_ = v___y_3262_;
v___y_3229_ = v___y_3265_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_nat_dec_le(v___y_3267_, v___y_3267_);
if (v___x_3272_ == 0)
{
if (v___x_3270_ == 0)
{
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
v___y_3228_ = v___y_3262_;
v___y_3229_ = v___y_3265_;
goto v___jp_3227_;
}
else
{
size_t v___x_3273_; size_t v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = ((size_t)0ULL);
v___x_3274_ = lean_usize_of_nat(v___y_3267_);
lean_dec(v___y_3267_);
v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_3263_, v___x_3273_, v___x_3274_, v___x_3271_, v___y_3266_, v___y_3268_, v___y_3264_, v___y_3269_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___y_3265_;
v___y_3251_ = v___x_3275_;
goto v___jp_3248_;
}
}
else
{
size_t v___x_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = lean_usize_of_nat(v___y_3267_);
lean_dec(v___y_3267_);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_3263_, v___x_3276_, v___x_3277_, v___x_3271_, v___y_3266_, v___y_3268_, v___y_3264_, v___y_3269_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___y_3263_);
v___y_3249_ = v___y_3262_;
v___y_3250_ = v___y_3265_;
v___y_3251_ = v___x_3278_;
goto v___jp_3248_;
}
}
}
v___jp_3279_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3284_, 0, v___y_3280_);
lean_ctor_set(v___x_3284_, 1, v___y_3283_);
lean_ctor_set(v___x_3284_, 2, v___y_3282_);
lean_ctor_set(v___x_3284_, 3, v___y_3281_);
v___x_3285_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
return v___x_3286_;
}
v___jp_3287_:
{
if (v___y_3293_ == 0)
{
lean_dec(v___y_3289_);
lean_dec_ref(v_code_2573_);
v___y_3280_ = v___y_3288_;
v___y_3281_ = v___y_3290_;
v___y_3282_ = v___y_3291_;
v___y_3283_ = v___y_3292_;
goto v___jp_3279_;
}
else
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_instBEqFVarId_beq(v___y_3289_, v___y_3291_);
lean_dec(v___y_3289_);
if (v___x_3294_ == 0)
{
lean_dec_ref(v_code_2573_);
v___y_3280_ = v___y_3288_;
v___y_3281_ = v___y_3290_;
v___y_3282_ = v___y_3291_;
v___y_3283_ = v___y_3292_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3295_; 
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3288_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_code_2573_);
return v___x_3295_;
}
}
}
v___jp_3296_:
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = lean_array_get_size(v___y_3300_);
v___x_3311_ = lean_nat_dec_lt(v___y_3298_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_code_2573_);
v___y_3261_ = v___y_3298_;
v___y_3262_ = v___y_3305_;
v___y_3263_ = v___y_3300_;
v___y_3264_ = v___y_3308_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___y_3306_;
v___y_3267_ = v___x_3310_;
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3309_;
goto v___jp_3260_;
}
else
{
if (v___x_3311_ == 0)
{
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_code_2573_);
v___y_3261_ = v___y_3298_;
v___y_3262_ = v___y_3305_;
v___y_3263_ = v___y_3300_;
v___y_3264_ = v___y_3308_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___y_3306_;
v___y_3267_ = v___x_3310_;
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3309_;
goto v___jp_3260_;
}
else
{
size_t v___x_3312_; size_t v___x_3313_; uint8_t v___x_3314_; 
v___x_3312_ = ((size_t)0ULL);
v___x_3313_ = lean_usize_of_nat(v___x_3310_);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_3300_, v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_code_2573_);
v___y_3261_ = v___y_3298_;
v___y_3262_ = v___y_3305_;
v___y_3263_ = v___y_3300_;
v___y_3264_ = v___y_3308_;
v___y_3265_ = v___y_3302_;
v___y_3266_ = v___y_3306_;
v___y_3267_ = v___x_3310_;
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3309_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3315_; 
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3298_);
lean_inc(v___y_3301_);
v___x_3315_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_3301_, v___y_3305_);
if (lean_obj_tag(v___x_3315_) == 0)
{
size_t v___x_3316_; size_t v___x_3317_; uint8_t v___x_3318_; 
lean_dec_ref_known(v___x_3315_, 1);
v___x_3316_ = lean_ptr_addr(v___y_3304_);
lean_dec_ref(v___y_3304_);
v___x_3317_ = lean_ptr_addr(v___y_3300_);
v___x_3318_ = lean_usize_dec_eq(v___x_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_dec_ref(v___y_3297_);
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3303_;
v___y_3290_ = v___y_3300_;
v___y_3291_ = v___y_3301_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___x_3318_;
goto v___jp_3287_;
}
else
{
size_t v___x_3319_; size_t v___x_3320_; uint8_t v___x_3321_; 
v___x_3319_ = lean_ptr_addr(v___y_3297_);
lean_dec_ref(v___y_3297_);
v___x_3320_ = lean_ptr_addr(v___y_3302_);
v___x_3321_ = lean_usize_dec_eq(v___x_3319_, v___x_3320_);
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3303_;
v___y_3290_ = v___y_3300_;
v___y_3291_ = v___y_3301_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___x_3321_;
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_code_2573_);
v_a_3322_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3315_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3315_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
}
v___jp_3330_:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v___x_3333_, 0);
lean_dec(v_unused_3341_);
v___x_3335_ = v___x_3333_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v___x_3333_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___y_3331_);
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___y_3331_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v___y_3331_);
v_a_3342_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3333_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3333_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
v___jp_3350_:
{
if (lean_obj_tag(v___y_3353_) == 0)
{
lean_dec_ref_known(v___y_3353_, 1);
v___y_3331_ = v___y_3351_;
v___y_3332_ = v___y_3352_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v___y_3351_);
v_a_3354_ = lean_ctor_get(v___y_3353_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___y_3353_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___y_3353_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___y_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
v___jp_3362_:
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_nat_dec_lt(v___y_3363_, v___y_3364_);
lean_dec(v___y_3363_);
if (v___x_3369_ == 0)
{
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3364_);
v___y_3331_ = v___y_3365_;
v___y_3332_ = v___y_3366_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_nat_dec_le(v___y_3364_, v___y_3364_);
if (v___x_3371_ == 0)
{
if (v___x_3369_ == 0)
{
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3364_);
v___y_3331_ = v___y_3365_;
v___y_3332_ = v___y_3366_;
goto v___jp_3330_;
}
else
{
size_t v___x_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = lean_usize_of_nat(v___y_3364_);
lean_dec(v___y_3364_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3367_, v___x_3372_, v___x_3373_, v___x_3370_, v___y_3368_);
lean_dec_ref(v___y_3367_);
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___y_3366_;
v___y_3353_ = v___x_3374_;
goto v___jp_3350_;
}
}
else
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = ((size_t)0ULL);
v___x_3376_ = lean_usize_of_nat(v___y_3364_);
lean_dec(v___y_3364_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3367_, v___x_3375_, v___x_3376_, v___x_3370_, v___y_3368_);
lean_dec_ref(v___y_3367_);
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___y_3366_;
v___y_3353_ = v___x_3377_;
goto v___jp_3350_;
}
}
}
v___jp_3378_:
{
switch(lean_obj_tag(v_code_2573_))
{
case 0:
{
lean_object* v_decl_3386_; lean_object* v_k_3387_; uint8_t v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
v_decl_3386_ = lean_ctor_get(v_code_2573_, 0);
v_k_3387_ = lean_ctor_get(v_code_2573_, 1);
v___x_3388_ = 0;
v___x_3389_ = 0;
lean_inc_ref(v_decl_3386_);
v___x_3390_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3388_, v___x_3389_, v_decl_3386_, v___y_3380_, v___y_3383_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; uint8_t v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3388_, v_decl_3386_, v_a_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3380_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_dec_ref_known(v___x_3393_, 1);
lean_inc_ref(v_decl_3386_);
lean_inc_ref(v_k_3387_);
v___y_3150_ = v___x_3388_;
v___y_3151_ = v_k_3387_;
v___y_3152_ = v_a_3391_;
v___y_3153_ = v_decl_3386_;
v___y_3154_ = v___y_3379_;
v___y_3155_ = v___y_3380_;
v___y_3156_ = v___y_3381_;
v___y_3157_ = v___y_3382_;
v___y_3158_ = v___y_3383_;
v___y_3159_ = v___y_3384_;
v___y_3160_ = v___y_3385_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_a_3391_);
lean_dec_ref_known(v_code_2573_, 2);
lean_dec_ref(v___y_3384_);
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_inc_ref(v_decl_3386_);
lean_inc_ref(v_k_3387_);
v___y_3150_ = v___x_3388_;
v___y_3151_ = v_k_3387_;
v___y_3152_ = v_a_3391_;
v___y_3153_ = v_decl_3386_;
v___y_3154_ = v___y_3379_;
v___y_3155_ = v___y_3380_;
v___y_3156_ = v___y_3381_;
v___y_3157_ = v___y_3382_;
v___y_3158_ = v___y_3383_;
v___y_3159_ = v___y_3384_;
v___y_3160_ = v___y_3385_;
goto v___jp_3149_;
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref_known(v_code_2573_, 2);
lean_dec_ref(v___y_3384_);
v_a_3402_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3390_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3390_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3410_; lean_object* v_args_3411_; lean_object* v___x_3412_; lean_object* v_subst_3413_; uint8_t v___x_3414_; uint8_t v___x_3415_; lean_object* v___x_3416_; 
v_fvarId_3410_ = lean_ctor_get(v_code_2573_, 0);
v_args_3411_ = lean_ctor_get(v_code_2573_, 1);
v___x_3412_ = lean_st_ref_get(v___y_3380_);
v_subst_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_subst_3413_);
lean_dec(v___x_3412_);
v___x_3414_ = 0;
v___x_3415_ = 0;
lean_inc(v_fvarId_3410_);
v___x_3416_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3413_, v_fvarId_3410_, v___x_3415_);
lean_dec_ref(v_subst_3413_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_fvarId_3417_; lean_object* v___x_3418_; 
v_fvarId_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_fvarId_3417_);
lean_dec_ref_known(v___x_3416_, 1);
lean_inc_ref(v_args_3411_);
v___x_3418_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3414_, v___x_3415_, v_args_3411_, v___y_3380_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_n(v_a_3419_, 2);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3417_, v_a_3419_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
if (lean_obj_tag(v_a_3421_) == 1)
{
lean_object* v_val_3422_; 
lean_dec(v_a_3419_);
lean_dec(v_fvarId_3417_);
lean_dec_ref_known(v_code_2573_, 2);
v_val_3422_ = lean_ctor_get(v_a_3421_, 0);
lean_inc(v_val_3422_);
lean_dec_ref_known(v_a_3421_, 1);
v_code_2573_ = v_val_3422_;
v_a_2574_ = v___y_3379_;
v_a_2575_ = v___y_3380_;
v_a_2576_ = v___y_3381_;
v_a_2577_ = v___y_3382_;
v_a_2578_ = v___y_3383_;
v_a_2579_ = v___y_3384_;
v_a_2580_ = v___y_3385_;
goto _start;
}
else
{
lean_object* v___x_3424_; 
lean_dec(v_a_3421_);
lean_dec_ref(v___y_3384_);
lean_inc(v_fvarId_3417_);
v___x_3424_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3417_, v___y_3380_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
lean_dec_ref_known(v___x_3424_, 1);
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_array_get_size(v_a_3419_);
v___x_3427_ = lean_nat_dec_lt(v___x_3425_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_inc_ref(v_args_3411_);
lean_inc(v_fvarId_3410_);
v___y_3205_ = v_fvarId_3417_;
v___y_3206_ = v_a_3419_;
v___y_3207_ = v_fvarId_3410_;
v___y_3208_ = v_args_3411_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = lean_nat_dec_le(v___x_3426_, v___x_3426_);
if (v___x_3429_ == 0)
{
if (v___x_3427_ == 0)
{
lean_inc_ref(v_args_3411_);
lean_inc(v_fvarId_3410_);
v___y_3205_ = v_fvarId_3417_;
v___y_3206_ = v_a_3419_;
v___y_3207_ = v_fvarId_3410_;
v___y_3208_ = v_args_3411_;
goto v___jp_3204_;
}
else
{
size_t v___x_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = lean_usize_of_nat(v___x_3426_);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3419_, v___x_3430_, v___x_3431_, v___x_3428_, v___y_3380_);
lean_inc_ref(v_args_3411_);
lean_inc(v_fvarId_3410_);
v___y_3214_ = v_fvarId_3417_;
v___y_3215_ = v_a_3419_;
v___y_3216_ = v_fvarId_3410_;
v___y_3217_ = v_args_3411_;
v___y_3218_ = v___x_3432_;
goto v___jp_3213_;
}
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = lean_usize_of_nat(v___x_3426_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3419_, v___x_3433_, v___x_3434_, v___x_3428_, v___y_3380_);
lean_inc_ref(v_args_3411_);
lean_inc(v_fvarId_3410_);
v___y_3214_ = v_fvarId_3417_;
v___y_3215_ = v_a_3419_;
v___y_3216_ = v_fvarId_3410_;
v___y_3217_ = v_args_3411_;
v___y_3218_ = v___x_3435_;
goto v___jp_3213_;
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_a_3419_);
lean_dec(v_fvarId_3417_);
lean_dec_ref_known(v_code_2573_, 2);
v_a_3436_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3424_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3424_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_3419_);
lean_dec(v_fvarId_3417_);
lean_dec_ref_known(v_code_2573_, 2);
lean_dec_ref(v___y_3384_);
v_a_3444_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3420_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3420_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v_fvarId_3417_);
lean_dec_ref_known(v_code_2573_, 2);
lean_dec_ref(v___y_3384_);
v_a_3452_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3418_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3418_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v___x_3460_; 
lean_dec_ref_known(v_code_2573_, 2);
v___x_3460_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3414_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec_ref(v___y_3384_);
return v___x_3460_;
}
}
case 4:
{
lean_object* v_cases_3461_; lean_object* v___x_3462_; 
v_cases_3461_ = lean_ctor_get(v_code_2573_, 0);
lean_inc_ref(v_cases_3461_);
v___x_3462_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3461_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3535_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3535_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3535_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
if (lean_obj_tag(v_a_3463_) == 1)
{
lean_object* v_val_3467_; lean_object* v___x_3469_; 
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_val_3467_ = lean_ctor_get(v_a_3463_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_a_3463_, 1);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_val_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_val_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
else
{
lean_object* v_typeName_3471_; lean_object* v_resultType_3472_; lean_object* v_discr_3473_; lean_object* v_alts_3474_; lean_object* v___x_3475_; lean_object* v_subst_3476_; uint8_t v___x_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; 
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
v_typeName_3471_ = lean_ctor_get(v_cases_3461_, 0);
v_resultType_3472_ = lean_ctor_get(v_cases_3461_, 1);
v_discr_3473_ = lean_ctor_get(v_cases_3461_, 2);
v_alts_3474_ = lean_ctor_get(v_cases_3461_, 3);
v___x_3475_ = lean_st_ref_get(v___y_3380_);
v_subst_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc_ref(v_subst_3476_);
lean_dec(v___x_3475_);
v___x_3477_ = 0;
v___x_3478_ = 0;
lean_inc(v_discr_3473_);
v___x_3479_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3476_, v_discr_3473_, v___x_3478_);
lean_dec_ref(v_subst_3476_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_fvarId_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_fvarId_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc_n(v_fvarId_3480_, 2);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = lean_st_ref_get(v___y_3380_);
v___x_3482_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3474_);
v___x_3483_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3480_, v___x_3482_, v_alts_3474_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3484_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3517_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3517_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3517_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_subst_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_subst_3490_ = lean_ctor_get(v___x_3481_, 0);
lean_inc_ref(v_subst_3490_);
lean_dec(v___x_3481_);
lean_inc_ref(v_resultType_3472_);
v___x_3491_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3477_, v_subst_3490_, v___x_3478_, v_resultType_3472_);
lean_dec_ref(v_subst_3490_);
v___x_3492_ = lean_array_get_size(v_a_3486_);
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_dec_eq(v___x_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_del_object(v___x_3488_);
lean_inc_ref(v_alts_3474_);
lean_inc(v_discr_3473_);
lean_inc(v_typeName_3471_);
lean_inc_ref(v_resultType_3472_);
v___y_3297_ = v_resultType_3472_;
v___y_3298_ = v___x_3482_;
v___y_3299_ = v_typeName_3471_;
v___y_3300_ = v_a_3486_;
v___y_3301_ = v_fvarId_3480_;
v___y_3302_ = v___x_3491_;
v___y_3303_ = v_discr_3473_;
v___y_3304_ = v_alts_3474_;
v___y_3305_ = v___y_3380_;
v___y_3306_ = v___y_3382_;
v___y_3307_ = v___y_3383_;
v___y_3308_ = v___y_3384_;
v___y_3309_ = v___y_3385_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_array_fget_borrowed(v_a_3486_, v___x_3482_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_params_3496_; lean_object* v_code_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
lean_del_object(v___x_3488_);
v_params_3496_ = lean_ctor_get(v___x_3495_, 1);
v_code_3497_ = lean_ctor_get(v___x_3495_, 2);
v___x_3498_ = lean_array_get_size(v_params_3496_);
v___x_3499_ = lean_nat_dec_lt(v___x_3482_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_inc_ref(v_code_3497_);
lean_inc_ref(v_params_3496_);
lean_dec_ref(v___x_3491_);
lean_dec(v_a_3486_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v___y_3363_ = v___x_3482_;
v___y_3364_ = v___x_3498_;
v___y_3365_ = v_code_3497_;
v___y_3366_ = v___y_3380_;
v___y_3367_ = v_params_3496_;
v___y_3368_ = v___y_3383_;
goto v___jp_3362_;
}
else
{
if (v___x_3499_ == 0)
{
lean_inc_ref(v_code_3497_);
lean_inc_ref(v_params_3496_);
lean_dec_ref(v___x_3491_);
lean_dec(v_a_3486_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v___y_3363_ = v___x_3482_;
v___y_3364_ = v___x_3498_;
v___y_3365_ = v_code_3497_;
v___y_3366_ = v___y_3380_;
v___y_3367_ = v_params_3496_;
v___y_3368_ = v___y_3383_;
goto v___jp_3362_;
}
else
{
size_t v___x_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((size_t)0ULL);
v___x_3501_ = lean_usize_of_nat(v___x_3498_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3496_, v___x_3500_, v___x_3501_, v___y_3380_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; uint8_t v___x_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = lean_unbox(v_a_3503_);
lean_dec(v_a_3503_);
if (v___x_3504_ == 0)
{
lean_inc_ref(v_code_3497_);
lean_inc_ref(v_params_3496_);
lean_dec_ref(v___x_3491_);
lean_dec(v_a_3486_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v___y_3363_ = v___x_3482_;
v___y_3364_ = v___x_3498_;
v___y_3365_ = v_code_3497_;
v___y_3366_ = v___y_3380_;
v___y_3367_ = v_params_3496_;
v___y_3368_ = v___y_3383_;
goto v___jp_3362_;
}
else
{
lean_inc_ref(v_alts_3474_);
lean_inc(v_discr_3473_);
lean_inc(v_typeName_3471_);
lean_inc_ref(v_resultType_3472_);
v___y_3297_ = v_resultType_3472_;
v___y_3298_ = v___x_3482_;
v___y_3299_ = v_typeName_3471_;
v___y_3300_ = v_a_3486_;
v___y_3301_ = v_fvarId_3480_;
v___y_3302_ = v___x_3491_;
v___y_3303_ = v_discr_3473_;
v___y_3304_ = v_alts_3474_;
v___y_3305_ = v___y_3380_;
v___y_3306_ = v___y_3382_;
v___y_3307_ = v___y_3383_;
v___y_3308_ = v___y_3384_;
v___y_3309_ = v___y_3385_;
goto v___jp_3296_;
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v___x_3491_);
lean_dec(v_a_3486_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_a_3505_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3502_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3502_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
else
{
lean_object* v_code_3513_; lean_object* v___x_3515_; 
lean_inc_ref(v___x_3495_);
lean_dec_ref(v___x_3491_);
lean_dec(v_a_3486_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_code_3513_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_code_3513_);
lean_dec_ref_known(v___x_3495_, 1);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_code_3513_);
v___x_3515_ = v___x_3488_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_code_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v___x_3481_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_a_3518_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3485_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3485_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v___x_3481_);
lean_dec(v_fvarId_3480_);
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_a_3526_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3483_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3483_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v___x_3534_; 
lean_dec_ref_known(v_code_2573_, 1);
v___x_3534_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3477_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec_ref(v___y_3384_);
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref_known(v_code_2573_, 1);
lean_dec_ref(v___y_3384_);
v_a_3536_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3462_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3462_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3544_; lean_object* v___x_3545_; lean_object* v_subst_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; 
v_fvarId_3544_ = lean_ctor_get(v_code_2573_, 0);
v___x_3545_ = lean_st_ref_get(v___y_3380_);
v_subst_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc_ref(v_subst_3546_);
lean_dec(v___x_3545_);
v___x_3547_ = 0;
lean_inc(v_fvarId_3544_);
v___x_3548_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3546_, v_fvarId_3544_, v___x_3547_);
lean_dec_ref(v_subst_3546_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_fvarId_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v___y_3384_);
v_fvarId_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc_n(v_fvarId_3549_, 2);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3549_, v___y_3380_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3569_; 
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3570_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3569_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3569_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
uint8_t v___x_3554_; 
v___x_3554_ = l_Lean_instBEqFVarId_beq(v_fvarId_3544_, v_fvarId_3549_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3564_; 
v_isSharedCheck_3564_ = !lean_is_exclusive(v_code_2573_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_code_2573_, 0);
lean_dec(v_unused_3565_);
v___x_3556_ = v_code_2573_;
v_isShared_3557_ = v_isSharedCheck_3564_;
goto v_resetjp_3555_;
}
else
{
lean_dec(v_code_2573_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3564_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v_fvarId_3549_);
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_fvarId_3549_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3559_);
v___x_3561_ = v___x_3552_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v___x_3567_; 
lean_dec(v_fvarId_3549_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v_code_2573_);
v___x_3567_ = v___x_3552_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_code_2573_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_fvarId_3549_);
lean_dec_ref_known(v_code_2573_, 1);
v_a_3571_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3550_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3550_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
uint8_t v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref_known(v_code_2573_, 1);
v___x_3579_ = 0;
v___x_3580_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3579_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec_ref(v___y_3384_);
return v___x_3580_;
}
}
case 6:
{
lean_object* v_type_3581_; lean_object* v___x_3582_; lean_object* v_subst_3583_; uint8_t v___x_3584_; uint8_t v___x_3585_; lean_object* v___x_3586_; size_t v___x_3587_; size_t v___x_3588_; uint8_t v___x_3589_; 
lean_dec_ref(v___y_3384_);
v_type_3581_ = lean_ctor_get(v_code_2573_, 0);
v___x_3582_ = lean_st_ref_get(v___y_3380_);
v_subst_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc_ref(v_subst_3583_);
lean_dec(v___x_3582_);
v___x_3584_ = 0;
v___x_3585_ = 0;
lean_inc_ref(v_type_3581_);
v___x_3586_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3584_, v_subst_3583_, v___x_3585_, v_type_3581_);
lean_dec_ref(v_subst_3583_);
v___x_3587_ = lean_ptr_addr(v_type_3581_);
v___x_3588_ = lean_ptr_addr(v___x_3586_);
v___x_3589_ = lean_usize_dec_eq(v___x_3587_, v___x_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3597_; 
v_isSharedCheck_3597_ = !lean_is_exclusive(v_code_2573_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v_code_2573_, 0);
lean_dec(v_unused_3598_);
v___x_3591_ = v_code_2573_;
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
else
{
lean_dec(v_code_2573_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3597_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3586_);
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3586_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
}
}
else
{
lean_object* v___x_3599_; 
lean_dec_ref(v___x_3586_);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_code_2573_);
return v___x_3599_;
}
}
default: 
{
lean_object* v_decl_3600_; lean_object* v_k_3601_; 
v_decl_3600_ = lean_ctor_get(v_code_2573_, 0);
v_k_3601_ = lean_ctor_get(v_code_2573_, 1);
lean_inc_ref(v_k_3601_);
lean_inc_ref(v_decl_3600_);
v_decl_2691_ = v_decl_3600_;
v_k_2692_ = v_k_3601_;
v___y_2693_ = v___y_3379_;
v___y_2694_ = v___y_3380_;
v___y_2695_ = v___y_3381_;
v___y_2696_ = v___y_3382_;
v___y_2697_ = v___y_3383_;
v___y_2698_ = v___y_3384_;
v___y_2699_ = v___y_3385_;
goto v___jp_2690_;
}
}
}
v___jp_3618_:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2575_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; lean_object* v_visited_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
lean_dec_ref_known(v___x_3619_, 1);
v___x_3620_ = lean_st_ref_get(v_a_2575_);
v_visited_3621_ = lean_ctor_get(v___x_3620_, 4);
lean_inc(v_visited_3621_);
lean_dec(v___x_3620_);
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_nat_add(v_currRecDepth_3605_, v___x_3622_);
lean_dec(v_currRecDepth_3605_);
v___x_3624_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3624_, 0, v_fileName_3602_);
lean_ctor_set(v___x_3624_, 1, v_fileMap_3603_);
lean_ctor_set(v___x_3624_, 2, v_options_3604_);
lean_ctor_set(v___x_3624_, 3, v___x_3623_);
lean_ctor_set(v___x_3624_, 4, v_maxRecDepth_3606_);
lean_ctor_set(v___x_3624_, 5, v_ref_3607_);
lean_ctor_set(v___x_3624_, 6, v_currNamespace_3608_);
lean_ctor_set(v___x_3624_, 7, v_openDecls_3609_);
lean_ctor_set(v___x_3624_, 8, v_initHeartbeats_3610_);
lean_ctor_set(v___x_3624_, 9, v_maxHeartbeats_3611_);
lean_ctor_set(v___x_3624_, 10, v_quotContext_3612_);
lean_ctor_set(v___x_3624_, 11, v_currMacroScope_3613_);
lean_ctor_set(v___x_3624_, 12, v_cancelTk_x3f_3615_);
lean_ctor_set(v___x_3624_, 13, v_inheritedTraceOptions_3617_);
lean_ctor_set_uint8(v___x_3624_, sizeof(void*)*14, v_diag_3614_);
lean_ctor_set_uint8(v___x_3624_, sizeof(void*)*14 + 1, v_suppressElabErrors_3616_);
v___x_3625_ = lean_unsigned_to_nat(128u);
v___x_3626_ = lean_nat_mod(v_visited_3621_, v___x_3625_);
lean_dec(v_visited_3621_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_nat_dec_eq(v___x_3626_, v___x_3627_);
lean_dec(v___x_3626_);
if (v___x_3628_ == 0)
{
v___y_3379_ = v_a_2574_;
v___y_3380_ = v_a_2575_;
v___y_3381_ = v_a_2576_;
v___y_3382_ = v_a_2577_;
v___y_3383_ = v_a_2578_;
v___y_3384_ = v___x_3624_;
v___y_3385_ = v_a_2580_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3630_ = l_Lean_Core_checkSystem(v___x_3629_, v___x_3624_, v_a_2580_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_dec_ref_known(v___x_3630_, 1);
v___y_3379_ = v_a_2574_;
v___y_3380_ = v_a_2575_;
v___y_3381_ = v_a_2576_;
v___y_3382_ = v_a_2577_;
v___y_3383_ = v_a_2578_;
v___y_3384_ = v___x_3624_;
v___y_3385_ = v_a_2580_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref_known(v___x_3624_, 14);
lean_dec_ref(v_code_2573_);
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_inheritedTraceOptions_3617_);
lean_dec(v_cancelTk_x3f_3615_);
lean_dec(v_currMacroScope_3613_);
lean_dec(v_quotContext_3612_);
lean_dec(v_maxHeartbeats_3611_);
lean_dec(v_initHeartbeats_3610_);
lean_dec(v_openDecls_3609_);
lean_dec(v_currNamespace_3608_);
lean_dec(v_ref_3607_);
lean_dec(v_maxRecDepth_3606_);
lean_dec(v_currRecDepth_3605_);
lean_dec_ref(v_options_3604_);
lean_dec_ref(v_fileMap_3603_);
lean_dec_ref(v_fileName_3602_);
lean_dec_ref(v_code_2573_);
v_a_3639_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3619_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3619_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_params_3660_; lean_object* v_type_3661_; lean_object* v_value_3662_; lean_object* v___x_3663_; lean_object* v_subst_3664_; uint8_t v___x_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_params_3660_ = lean_ctor_get(v_decl_3651_, 2);
v_type_3661_ = lean_ctor_get(v_decl_3651_, 3);
v_value_3662_ = lean_ctor_get(v_decl_3651_, 4);
v___x_3663_ = lean_st_ref_get(v_a_3653_);
v_subst_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc_ref(v_subst_3664_);
lean_dec(v___x_3663_);
v___x_3665_ = 0;
v___x_3666_ = 0;
lean_inc_ref(v_type_3661_);
v___x_3667_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3665_, v_subst_3664_, v___x_3666_, v_type_3661_);
lean_dec_ref(v_subst_3664_);
lean_inc_ref(v_params_3660_);
v___x_3668_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3665_, v___x_3666_, v_params_3660_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
lean_inc_ref(v_a_3657_);
lean_inc_ref(v_value_3662_);
v___x_3670_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3662_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v___x_3672_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3665_, v_decl_3651_, v___x_3667_, v_a_3669_, v_a_3671_, v_a_3656_);
return v___x_3672_;
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3669_);
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_decl_3651_);
v_a_3673_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3670_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3670_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_decl_3651_);
v_a_3681_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3668_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3668_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3699_, lean_object* v_i_3700_, lean_object* v_as_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3699_, v_i_3700_, v_as_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec_ref(v_a_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3721_, lean_object* v_k_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3721_, v_k_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3742_, uint8_t v_t_3743_, lean_object* v_decl_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3742_, v_t_3743_, v_decl_3744_, v___y_3746_, v___y_3749_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3754_, lean_object* v_t_3755_, lean_object* v_decl_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_pu_boxed_3765_; uint8_t v_t_boxed_3766_; lean_object* v_res_3767_; 
v_pu_boxed_3765_ = lean_unbox(v_pu_3754_);
v_t_boxed_3766_ = lean_unbox(v_t_3755_);
v_res_3767_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3765_, v_t_boxed_3766_, v_decl_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3768_, uint8_t v_t_3769_, lean_object* v_args_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3768_, v_t_3769_, v_args_3770_, v___y_3772_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3780_, lean_object* v_t_3781_, lean_object* v_args_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_pu_boxed_3791_; uint8_t v_t_boxed_3792_; lean_object* v_res_3793_; 
v_pu_boxed_3791_ = lean_unbox(v_pu_3780_);
v_t_boxed_3792_ = lean_unbox(v_t_3781_);
v_res_3793_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3791_, v_t_boxed_3792_, v_args_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3794_, lean_object* v_R_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3796_, v_b_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3799_, lean_object* v_x_3800_, lean_object* v_x_3801_, lean_object* v_x_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3800_, v_x_3801_, v_x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3804_, size_t v_i_3805_, size_t v_stop_3806_, lean_object* v_b_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3804_, v_i_3805_, v_stop_3806_, v_b_3807_, v___y_3809_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3817_, lean_object* v_i_3818_, lean_object* v_stop_3819_, lean_object* v_b_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
size_t v_i_boxed_3829_; size_t v_stop_boxed_3830_; lean_object* v_res_3831_; 
v_i_boxed_3829_ = lean_unbox_usize(v_i_3818_);
lean_dec(v_i_3818_);
v_stop_boxed_3830_ = lean_unbox_usize(v_stop_3819_);
lean_dec(v_stop_3819_);
v_res_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3817_, v_i_boxed_3829_, v_stop_boxed_3830_, v_b_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v_as_3817_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3832_, size_t v_i_3833_, size_t v_stop_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3832_, v_i_3833_, v_stop_3834_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3844_, lean_object* v_i_3845_, lean_object* v_stop_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
size_t v_i_boxed_3855_; size_t v_stop_boxed_3856_; lean_object* v_res_3857_; 
v_i_boxed_3855_ = lean_unbox_usize(v_i_3845_);
lean_dec(v_i_3845_);
v_stop_boxed_3856_ = lean_unbox_usize(v_stop_3846_);
lean_dec(v_stop_3846_);
v_res_3857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3844_, v_i_boxed_3855_, v_stop_boxed_3856_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v_as_3844_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3858_, size_t v_i_3859_, size_t v_stop_3860_, lean_object* v_b_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3858_, v_i_3859_, v_stop_3860_, v_b_3861_, v___y_3863_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3868_, lean_object* v_i_3869_, lean_object* v_stop_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
size_t v_i_boxed_3877_; size_t v_stop_boxed_3878_; lean_object* v_res_3879_; 
v_i_boxed_3877_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_stop_boxed_3878_ = lean_unbox_usize(v_stop_3870_);
lean_dec(v_stop_3870_);
v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3868_, v_i_boxed_3877_, v_stop_boxed_3878_, v_b_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v_as_3868_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3880_, size_t v_i_3881_, size_t v_stop_3882_, lean_object* v_b_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3880_, v_i_3881_, v_stop_3882_, v_b_3883_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3893_, lean_object* v_i_3894_, lean_object* v_stop_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
size_t v_i_boxed_3905_; size_t v_stop_boxed_3906_; lean_object* v_res_3907_; 
v_i_boxed_3905_ = lean_unbox_usize(v_i_3894_);
lean_dec(v_i_3894_);
v_stop_boxed_3906_ = lean_unbox_usize(v_stop_3895_);
lean_dec(v_stop_3895_);
v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3893_, v_i_boxed_3905_, v_stop_boxed_3906_, v_b_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_as_3893_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3908_, size_t v_i_3909_, size_t v_stop_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3908_, v_i_3909_, v_stop_3910_, v_b_3911_, v___y_3916_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3921_, lean_object* v_i_3922_, lean_object* v_stop_3923_, lean_object* v_b_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
size_t v_i_boxed_3933_; size_t v_stop_boxed_3934_; lean_object* v_res_3935_; 
v_i_boxed_3933_ = lean_unbox_usize(v_i_3922_);
lean_dec(v_i_3922_);
v_stop_boxed_3934_ = lean_unbox_usize(v_stop_3923_);
lean_dec(v_stop_3923_);
v_res_3935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3921_, v_i_boxed_3933_, v_stop_boxed_3934_, v_b_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v_as_3921_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3936_, size_t v_i_3937_, size_t v_stop_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3936_, v_i_3937_, v_stop_3938_, v___y_3940_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3948_, lean_object* v_i_3949_, lean_object* v_stop_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_i_boxed_3959_; size_t v_stop_boxed_3960_; lean_object* v_res_3961_; 
v_i_boxed_3959_ = lean_unbox_usize(v_i_3949_);
lean_dec(v_i_3949_);
v_stop_boxed_3960_ = lean_unbox_usize(v_stop_3950_);
lean_dec(v_stop_3950_);
v_res_3961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3948_, v_i_boxed_3959_, v_stop_boxed_3960_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec_ref(v_as_3948_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3962_, size_t v_sz_3963_, size_t v_i_3964_, lean_object* v_b_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3962_, v_sz_3963_, v_i_3964_, v_b_3965_, v___y_3967_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3975_, lean_object* v_sz_3976_, lean_object* v_i_3977_, lean_object* v_b_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
size_t v_sz_boxed_3987_; size_t v_i_boxed_3988_; lean_object* v_res_3989_; 
v_sz_boxed_3987_ = lean_unbox_usize(v_sz_3976_);
lean_dec(v_sz_3976_);
v_i_boxed_3988_ = lean_unbox_usize(v_i_3977_);
lean_dec(v_i_3977_);
v_res_3989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3975_, v_sz_boxed_3987_, v_i_boxed_3988_, v_b_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v_as_3975_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3990_, lean_object* v_x_3991_, size_t v_x_3992_, size_t v_x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3991_, v_x_3992_, v_x_3993_, v_x_3994_, v_x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3997_, lean_object* v_x_3998_, lean_object* v_x_3999_, lean_object* v_x_4000_, lean_object* v_x_4001_, lean_object* v_x_4002_){
_start:
{
size_t v_x_56585__boxed_4003_; size_t v_x_56586__boxed_4004_; lean_object* v_res_4005_; 
v_x_56585__boxed_4003_ = lean_unbox_usize(v_x_3999_);
lean_dec(v_x_3999_);
v_x_56586__boxed_4004_ = lean_unbox_usize(v_x_4000_);
lean_dec(v_x_4000_);
v_res_4005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3997_, v_x_3998_, v_x_56585__boxed_4003_, v_x_56586__boxed_4004_, v_x_4001_, v_x_4002_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_4006_, uint8_t v_t_4007_, lean_object* v_i_4008_, lean_object* v_as_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_4006_, v_t_4007_, v_i_4008_, v_as_4009_, v___y_4011_, v___y_4014_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_4019_, lean_object* v_t_4020_, lean_object* v_i_4021_, lean_object* v_as_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
uint8_t v_pu_boxed_4031_; uint8_t v_t_boxed_4032_; lean_object* v_res_4033_; 
v_pu_boxed_4031_ = lean_unbox(v_pu_4019_);
v_t_boxed_4032_ = lean_unbox(v_t_4020_);
v_res_4033_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_4031_, v_t_boxed_4032_, v_i_4021_, v_as_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_4034_, lean_object* v_n_4035_, lean_object* v_k_4036_, lean_object* v_v_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_4035_, v_k_4036_, v_v_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_4039_, size_t v_depth_4040_, lean_object* v_keys_4041_, lean_object* v_vals_4042_, lean_object* v_heq_4043_, lean_object* v_i_4044_, lean_object* v_entries_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_4040_, v_keys_4041_, v_vals_4042_, v_i_4044_, v_entries_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_4047_, lean_object* v_depth_4048_, lean_object* v_keys_4049_, lean_object* v_vals_4050_, lean_object* v_heq_4051_, lean_object* v_i_4052_, lean_object* v_entries_4053_){
_start:
{
size_t v_depth_boxed_4054_; lean_object* v_res_4055_; 
v_depth_boxed_4054_ = lean_unbox_usize(v_depth_4048_);
lean_dec(v_depth_4048_);
v_res_4055_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_4047_, v_depth_boxed_4054_, v_keys_4049_, v_vals_4050_, v_heq_4051_, v_i_4052_, v_entries_4053_);
lean_dec_ref(v_vals_4050_);
lean_dec_ref(v_keys_4049_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_4056_, lean_object* v_x_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_, lean_object* v_x_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_4057_, v_x_4058_, v_x_4059_, v_x_4060_);
return v___x_4061_;
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
