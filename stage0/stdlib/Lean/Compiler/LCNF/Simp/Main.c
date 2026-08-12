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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_nbuckets_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_84_ = lean_array_get_size(v_data_83_);
v___x_85_ = lean_unsigned_to_nat(2u);
v_nbuckets_86_ = lean_nat_mul(v___x_84_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_box(0);
v___x_89_ = lean_mk_array(v_nbuckets_86_, v___x_88_);
v___x_90_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_87_, v_data_83_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object* v_a_91_, lean_object* v_b_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_dec(v_b_92_);
lean_dec(v_a_91_);
return v_x_93_;
}
else
{
lean_object* v_key_94_; lean_object* v_value_95_; lean_object* v_tail_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_108_; 
v_key_94_ = lean_ctor_get(v_x_93_, 0);
v_value_95_ = lean_ctor_get(v_x_93_, 1);
v_tail_96_ = lean_ctor_get(v_x_93_, 2);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_108_ == 0)
{
v___x_98_ = v_x_93_;
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_tail_96_);
lean_inc(v_value_95_);
lean_inc(v_key_94_);
lean_dec(v_x_93_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_instBEqFVarId_beq(v_key_94_, v_a_91_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_91_, v_b_92_, v_tail_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 2, v___x_101_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_key_94_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_value_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v___x_106_; 
lean_dec(v_value_95_);
lean_dec(v_key_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_b_92_);
lean_ctor_set(v___x_98_, 0, v_a_91_);
v___x_106_ = v___x_98_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_91_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_b_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_tail_96_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* v_m_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v_size_112_; lean_object* v_buckets_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_156_; 
v_size_112_ = lean_ctor_get(v_m_109_, 0);
v_buckets_113_ = lean_ctor_get(v_m_109_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_m_109_);
if (v_isSharedCheck_156_ == 0)
{
v___x_115_ = v_m_109_;
v_isShared_116_ = v_isSharedCheck_156_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_buckets_113_);
lean_inc(v_size_112_);
lean_dec(v_m_109_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_156_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v_fold_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v_bkt_130_; uint8_t v___x_131_; 
v___x_117_ = lean_array_get_size(v_buckets_113_);
v___x_118_ = l_Lean_instHashableFVarId_hash(v_a_110_);
v___x_119_ = 32ULL;
v___x_120_ = lean_uint64_shift_right(v___x_118_, v___x_119_);
v_fold_121_ = lean_uint64_xor(v___x_118_, v___x_120_);
v___x_122_ = 16ULL;
v___x_123_ = lean_uint64_shift_right(v_fold_121_, v___x_122_);
v___x_124_ = lean_uint64_xor(v_fold_121_, v___x_123_);
v___x_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = lean_usize_of_nat(v___x_117_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_sub(v___x_126_, v___x_127_);
v___x_129_ = lean_usize_land(v___x_125_, v___x_128_);
v_bkt_130_ = lean_array_uget_borrowed(v_buckets_113_, v___x_129_);
v___x_131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_110_, v_bkt_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v_size_x27_133_; lean_object* v___x_134_; lean_object* v_buckets_x27_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v_size_x27_133_ = lean_nat_add(v_size_112_, v___x_132_);
lean_dec(v_size_112_);
lean_inc(v_bkt_130_);
v___x_134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_134_, 0, v_a_110_);
lean_ctor_set(v___x_134_, 1, v_b_111_);
lean_ctor_set(v___x_134_, 2, v_bkt_130_);
v_buckets_x27_135_ = lean_array_uset(v_buckets_113_, v___x_129_, v___x_134_);
v___x_136_ = lean_unsigned_to_nat(4u);
v___x_137_ = lean_nat_mul(v_size_x27_133_, v___x_136_);
v___x_138_ = lean_unsigned_to_nat(3u);
v___x_139_ = lean_nat_div(v___x_137_, v___x_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_array_get_size(v_buckets_x27_135_);
v___x_141_ = lean_nat_dec_le(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
if (v___x_141_ == 0)
{
lean_object* v_val_142_; lean_object* v___x_144_; 
v_val_142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_buckets_x27_135_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_val_142_);
lean_ctor_set(v___x_115_, 0, v_size_x27_133_);
v___x_144_ = v___x_115_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_size_x27_133_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_val_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
else
{
lean_object* v___x_147_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_buckets_x27_135_);
lean_ctor_set(v___x_115_, 0, v_size_x27_133_);
v___x_147_ = v___x_115_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_size_x27_133_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_buckets_x27_135_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v___x_149_; lean_object* v_buckets_x27_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_inc(v_bkt_130_);
v___x_149_ = lean_box(0);
v_buckets_x27_150_ = lean_array_uset(v_buckets_113_, v___x_129_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_110_, v_b_111_, v_bkt_130_);
v___x_152_ = lean_array_uset(v_buckets_x27_150_, v___x_129_, v___x_151_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_152_);
v___x_154_ = v___x_115_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_112_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* v_as_157_, size_t v_sz_158_, size_t v_i_159_, lean_object* v_b_160_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v_b_160_);
return v___x_163_;
}
else
{
lean_object* v_snd_164_; lean_object* v_fst_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_199_; 
v_snd_164_ = lean_ctor_get(v_b_160_, 1);
v_fst_165_ = lean_ctor_get(v_b_160_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_b_160_);
if (v_isSharedCheck_199_ == 0)
{
v___x_167_ = v_b_160_;
v_isShared_168_ = v_isSharedCheck_199_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_snd_164_);
lean_inc(v_fst_165_);
lean_dec(v_b_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_199_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_array_169_; lean_object* v_start_170_; lean_object* v_stop_171_; uint8_t v___x_172_; 
v_array_169_ = lean_ctor_get(v_snd_164_, 0);
v_start_170_ = lean_ctor_get(v_snd_164_, 1);
v_stop_171_ = lean_ctor_get(v_snd_164_, 2);
v___x_172_ = lean_nat_dec_lt(v_start_170_, v_stop_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_174_; 
if (v_isShared_168_ == 0)
{
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_fst_165_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_snd_164_);
v___x_174_ = v_reuseFailAlloc_176_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
else
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_195_; 
lean_inc(v_stop_171_);
lean_inc(v_start_170_);
lean_inc_ref(v_array_169_);
v_isSharedCheck_195_ = !lean_is_exclusive(v_snd_164_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_196_ = lean_ctor_get(v_snd_164_, 2);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v_snd_164_, 1);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_snd_164_, 0);
lean_dec(v_unused_198_);
v___x_178_ = v_snd_164_;
v_isShared_179_ = v_isSharedCheck_195_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_snd_164_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_195_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_a_180_; lean_object* v_fvarId_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v_a_180_ = lean_array_uget_borrowed(v_as_157_, v_i_159_);
v_fvarId_181_ = lean_ctor_get(v_a_180_, 0);
v___x_182_ = lean_array_fget(v_array_169_, v_start_170_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_start_170_, v___x_183_);
lean_dec(v_start_170_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_184_);
v___x_186_ = v___x_178_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_array_169_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_stop_171_);
v___x_186_ = v_reuseFailAlloc_194_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_inc(v_fvarId_181_);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_165_, v_fvarId_181_, v___x_182_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_186_);
lean_ctor_set(v___x_167_, 0, v___x_187_);
v___x_189_ = v___x_167_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_186_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
size_t v___x_190_; size_t v___x_191_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_159_, v___x_190_);
v_i_159_ = v___x_191_;
v_b_160_ = v___x_189_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* v_as_200_, lean_object* v_sz_201_, lean_object* v_i_202_, lean_object* v_b_203_, lean_object* v___y_204_){
_start:
{
size_t v_sz_boxed_205_; size_t v_i_boxed_206_; lean_object* v_res_207_; 
v_sz_boxed_205_ = lean_unbox_usize(v_sz_201_);
lean_dec(v_sz_201_);
v_i_boxed_206_ = lean_unbox_usize(v_i_202_);
lean_dec(v_i_202_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_200_, v_sz_boxed_205_, v_i_boxed_206_, v_b_203_);
lean_dec_ref(v_as_200_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* v_a_208_, lean_object* v_b_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_array_215_; lean_object* v_start_216_; lean_object* v_stop_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_267_; 
v_array_215_ = lean_ctor_get(v_a_208_, 0);
v_start_216_ = lean_ctor_get(v_a_208_, 1);
v_stop_217_ = lean_ctor_get(v_a_208_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_a_208_);
if (v_isSharedCheck_267_ == 0)
{
v___x_219_ = v_a_208_;
v_isShared_220_ = v_isSharedCheck_267_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_stop_217_);
lean_inc(v_start_216_);
lean_inc(v_array_215_);
lean_dec(v_a_208_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_267_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; 
v___x_221_ = lean_nat_dec_lt(v_start_216_, v_stop_217_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_del_object(v___x_219_);
lean_dec(v_stop_217_);
lean_dec(v_start_216_);
lean_dec_ref(v_array_215_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v_b_209_);
return v___x_222_;
}
else
{
lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_266_; 
v_fst_223_ = lean_ctor_get(v_b_209_, 0);
v_snd_224_ = lean_ctor_get(v_b_209_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_b_209_);
if (v_isSharedCheck_266_ == 0)
{
v___x_226_ = v_b_209_;
v_isShared_227_ = v_isSharedCheck_266_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_snd_224_);
lean_inc(v_fst_223_);
lean_dec(v_b_209_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_266_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v_fvarId_229_; lean_object* v_type_230_; uint8_t v___x_231_; lean_object* v___x_232_; 
v___x_228_ = lean_array_fget_borrowed(v_array_215_, v_start_216_);
v_fvarId_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_fvarId_229_);
v_type_230_ = lean_ctor_get(v___x_228_, 2);
v___x_231_ = 0;
lean_inc_ref(v_type_230_);
v___x_232_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v___x_231_, v_type_230_, v_fst_223_, v___x_221_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = 0;
v___x_235_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_231_, v_a_233_, v___x_234_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v_fvarId_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v_fvarId_237_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_fvarId_237_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_start_216_, v___x_238_);
lean_dec(v_start_216_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_239_);
v___x_241_ = v___x_219_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_array_215_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_stop_217_);
v___x_241_ = v_reuseFailAlloc_249_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_242_ = lean_array_push(v_snd_224_, v_a_236_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_fvarId_237_);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_223_, v_fvarId_229_, v___x_243_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_242_);
lean_ctor_set(v___x_226_, 0, v___x_244_);
v___x_246_ = v___x_226_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_242_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_a_208_ = v___x_241_;
v_b_209_ = v___x_246_;
goto _start;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_fvarId_229_);
lean_del_object(v___x_226_);
lean_dec(v_snd_224_);
lean_dec(v_fst_223_);
lean_del_object(v___x_219_);
lean_dec(v_stop_217_);
lean_dec(v_start_216_);
lean_dec_ref(v_array_215_);
v_a_250_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_235_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_235_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v_fvarId_229_);
lean_del_object(v___x_226_);
lean_dec(v_snd_224_);
lean_dec(v_fst_223_);
lean_del_object(v___x_219_);
lean_dec(v_stop_217_);
lean_dec(v_start_216_);
lean_dec_ref(v_array_215_);
v_a_258_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_232_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_232_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_268_, v_b_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_unsigned_to_nat(16u);
v___x_278_ = lean_mk_array(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_subst_281_; 
v___x_279_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
v___x_280_ = lean_unsigned_to_nat(0u);
v_subst_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_subst_281_, 0, v___x_280_);
lean_ctor_set(v_subst_281_, 1, v___x_279_);
return v_subst_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* v_info_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_params_296_; lean_object* v_value_297_; lean_object* v_args_298_; lean_object* v___x_299_; lean_object* v_subst_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; size_t v_sz_304_; size_t v___x_305_; lean_object* v___x_306_; 
v_params_296_ = lean_ctor_get(v_info_287_, 0);
lean_inc_ref(v_params_296_);
v_value_297_ = lean_ctor_get(v_info_287_, 1);
lean_inc_ref(v_value_297_);
v_args_298_ = lean_ctor_get(v_info_287_, 3);
lean_inc_ref(v_args_298_);
lean_dec_ref(v_info_287_);
v___x_299_ = lean_unsigned_to_nat(0u);
v_subst_300_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
v___x_301_ = lean_array_get_size(v_args_298_);
v___x_302_ = l_Array_toSubarray___redArg(v_args_298_, v___x_299_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_subst_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v_sz_304_ = lean_array_size(v_params_296_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_params_296_, v_sz_304_, v___x_305_, v___x_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_fst_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_357_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v_fst_308_ = lean_ctor_get(v_a_307_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_a_307_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_a_307_, 1);
lean_dec(v_unused_358_);
v___x_310_ = v_a_307_;
v_isShared_311_ = v_isSharedCheck_357_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_fst_308_);
lean_dec(v_a_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_357_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_lower_314_; lean_object* v_upper_315_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_312_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2));
v___x_355_ = lean_array_get_size(v_params_296_);
v___x_356_ = lean_nat_dec_le(v___x_301_, v___x_299_);
if (v___x_356_ == 0)
{
v_lower_314_ = v___x_301_;
v_upper_315_ = v___x_355_;
goto v___jp_313_;
}
else
{
v_lower_314_ = v___x_299_;
v_upper_315_ = v___x_355_;
goto v___jp_313_;
}
v___jp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = l_Array_toSubarray___redArg(v_params_296_, v_lower_314_, v_upper_315_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_312_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_fst_308_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_312_);
v___x_318_ = v_reuseFailAlloc_354_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v___x_316_, v___x_318_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; uint8_t v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v_fst_321_ = lean_ctor_get(v_a_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v_a_320_, 1);
lean_inc(v_snd_322_);
lean_dec(v_a_320_);
v___x_323_ = 0;
v___x_324_ = 0;
v___x_325_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_323_, v_value_297_, v_fst_321_, v___x_324_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_n(v_a_326_, 2);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_326_, v___x_324_, v_a_289_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref_known(v___x_327_, 1);
v___x_328_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_329_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_snd_322_, v_a_326_, v___x_328_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_326_);
lean_dec(v_snd_322_);
v_a_330_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_327_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_snd_322_);
v_a_338_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_325_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_325_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v_value_297_);
v_a_346_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_319_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_319_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_value_297_);
lean_dec_ref(v_params_296_);
v_a_359_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_306_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_306_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* v_info_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_info_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* v_00_u03b2_377_, lean_object* v_m_378_, lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_378_, v_a_379_, v_b_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* v_as_382_, size_t v_sz_383_, size_t v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_382_, v_sz_383_, v_i_384_, v_b_385_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* v_as_395_, lean_object* v_sz_396_, lean_object* v_i_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
size_t v_sz_boxed_407_; size_t v_i_boxed_408_; lean_object* v_res_409_; 
v_sz_boxed_407_ = lean_unbox_usize(v_sz_396_);
lean_dec(v_sz_396_);
v_i_boxed_408_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_395_, v_sz_boxed_407_, v_i_boxed_408_, v_b_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec_ref(v_as_395_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* v_inst_410_, lean_object* v_R_411_, lean_object* v_a_412_, lean_object* v_b_413_, lean_object* v_c_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_412_, v_b_413_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* v_inst_424_, lean_object* v_R_425_, lean_object* v_a_426_, lean_object* v_b_427_, lean_object* v_c_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(v_inst_424_, v_R_425_, v_a_426_, v_b_427_, v_c_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_442_, v_a_443_, v_x_444_);
lean_dec(v_x_444_);
lean_dec(v_a_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* v_00_u03b2_447_, lean_object* v_data_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_data_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_b_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_451_, v_b_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_455_, lean_object* v_i_456_, lean_object* v_source_457_, lean_object* v_target_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v_i_456_, v_source_457_, v_target_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* v_fvarId_464_, lean_object* v_args_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; 
v___x_474_ = 0;
v___x_475_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_474_, v_fvarId_464_, v_a_470_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_540_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_540_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_540_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_540_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
if (lean_obj_tag(v_a_476_) == 1)
{
lean_object* v_val_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_478_);
v_val_480_ = lean_ctor_get(v_a_476_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_535_ == 0)
{
v___x_482_ = v_a_476_;
v_isShared_483_ = v_isSharedCheck_535_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_val_480_);
lean_dec(v_a_476_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_535_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_val_480_, v_a_467_, v_a_469_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_526_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_526_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_526_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_526_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint8_t v___x_489_; 
v___x_489_ = lean_unbox(v_a_485_);
lean_dec(v_a_485_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_del_object(v___x_482_);
lean_dec(v_val_480_);
lean_dec_ref(v_args_465_);
v___x_490_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_490_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_494_; 
lean_del_object(v___x_487_);
v___x_494_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_467_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_params_495_; lean_object* v_value_496_; uint8_t v___x_497_; lean_object* v___x_498_; 
lean_dec_ref_known(v___x_494_, 1);
v_params_495_ = lean_ctor_get(v_val_480_, 2);
lean_inc_ref(v_params_495_);
v_value_496_ = lean_ctor_get(v_val_480_, 4);
lean_inc_ref(v_value_496_);
lean_dec(v_val_480_);
v___x_497_ = 0;
v___x_498_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_495_, v_value_496_, v_args_465_, v___x_497_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec_ref(v_params_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_509_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_509_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_a_499_);
v___x_504_ = v___x_482_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_482_);
v_a_510_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_498_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_498_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_482_);
lean_dec(v_val_480_);
lean_dec_ref(v_args_465_);
v_a_518_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_494_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_494_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_482_);
lean_dec(v_val_480_);
lean_dec_ref(v_args_465_);
v_a_527_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_484_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_484_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_538_; 
lean_dec(v_a_476_);
lean_dec_ref(v_args_465_);
v___x_536_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_536_);
v___x_538_ = v___x_478_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_args_465_);
v_a_541_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_475_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_475_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* v_fvarId_549_, lean_object* v_args_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_549_, v_args_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_fvarId_549_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* v_declName_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_env_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = lean_st_ref_get(v___y_561_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_563_);
v___x_565_ = l_Lean_isInstanceReducibleCore(v_env_564_, v_declName_560_);
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_569_, v___y_570_);
lean_dec(v___y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* v_declName_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_573_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* v_declName_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t v_sz_593_, size_t v_i_594_, lean_object* v_bs_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = lean_usize_dec_lt(v_i_594_, v_sz_593_);
if (v___x_596_ == 0)
{
return v_bs_595_;
}
else
{
lean_object* v_v_597_; lean_object* v_fvarId_598_; lean_object* v___x_599_; lean_object* v_bs_x27_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v_v_597_ = lean_array_uget_borrowed(v_bs_595_, v_i_594_);
v_fvarId_598_ = lean_ctor_get(v_v_597_, 0);
lean_inc(v_fvarId_598_);
v___x_599_ = lean_unsigned_to_nat(0u);
v_bs_x27_600_ = lean_array_uset(v_bs_595_, v_i_594_, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_fvarId_598_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_594_, v___x_602_);
v___x_604_ = lean_array_uset(v_bs_x27_600_, v_i_594_, v___x_601_);
v_i_594_ = v___x_603_;
v_bs_595_ = v___x_604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_bs_608_){
_start:
{
size_t v_sz_boxed_609_; size_t v_i_boxed_610_; lean_object* v_res_611_; 
v_sz_boxed_609_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_610_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_609_, v_i_boxed_610_, v_bs_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* v_letDecl_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_config_624_; uint8_t v_etaPoly_625_; 
v_config_624_ = lean_ctor_get(v_a_616_, 1);
v_etaPoly_625_ = lean_ctor_get_uint8(v_config_624_, 0);
if (v_etaPoly_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_letDecl_615_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v_value_628_; 
v_value_628_ = lean_ctor_get(v_letDecl_615_, 3);
lean_inc(v_value_628_);
if (lean_obj_tag(v_value_628_) == 3)
{
lean_object* v_fvarId_629_; lean_object* v_type_630_; lean_object* v_declName_631_; lean_object* v_us_632_; lean_object* v_args_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_802_; 
v_fvarId_629_ = lean_ctor_get(v_letDecl_615_, 0);
v_type_630_ = lean_ctor_get(v_letDecl_615_, 2);
v_declName_631_ = lean_ctor_get(v_value_628_, 0);
v_us_632_ = lean_ctor_get(v_value_628_, 1);
v_args_633_ = lean_ctor_get(v_value_628_, 2);
v_isSharedCheck_802_ = !lean_is_exclusive(v_value_628_);
if (v_isSharedCheck_802_ == 0)
{
v___x_635_ = v_value_628_;
v_isShared_636_ = v_isSharedCheck_802_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_args_633_);
lean_inc(v_us_632_);
lean_inc(v_declName_631_);
lean_dec(v_value_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_802_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v_env_638_; uint8_t v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_st_ref_get(v_a_622_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_637_);
v___x_639_ = 0;
lean_inc(v_declName_631_);
v___x_640_ = l_Lean_Environment_find_x3f(v_env_638_, v_declName_631_, v___x_639_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = l_Lean_ConstantInfo_type(v_val_641_);
lean_dec(v_val_641_);
v___x_643_ = l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_642_, v_a_622_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_791_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_791_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_791_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_791_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = lean_unbox(v_a_644_);
lean_dec(v_a_644_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_649_ = lean_box(0);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
else
{
lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_790_; 
lean_del_object(v___x_646_);
lean_inc(v_declName_631_);
v___x_653_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_631_, v_a_622_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_790_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_790_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_790_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_789_; 
v_val_658_ = lean_ctor_get(v_a_654_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_789_ == 0)
{
v___x_660_ = v_a_654_;
v_isShared_661_ = v_isSharedCheck_789_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v_a_654_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_789_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v___x_662_; 
v___x_662_ = lean_unbox(v_val_658_);
lean_dec(v_val_658_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_del_object(v___x_656_);
v___x_663_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_619_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_776_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_776_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_776_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_776_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
uint8_t v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_unbox(v_a_664_);
lean_inc(v_declName_631_);
v___x_669_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_631_, v___x_668_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_767_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_767_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_767_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_767_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
if (lean_obj_tag(v_a_670_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_766_; 
v_val_679_ = lean_ctor_get(v_a_670_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_766_ == 0)
{
v___x_681_ = v_a_670_;
v_isShared_682_ = v_isSharedCheck_766_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_val_679_);
lean_dec(v_a_670_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_766_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
uint8_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unbox(v_a_664_);
lean_dec(v_a_664_);
v___x_684_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_del_object(v___x_672_);
v___x_685_ = lean_array_get_size(v_args_633_);
v___x_686_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_679_);
lean_dec(v_val_679_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
lean_dec(v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_del_object(v___x_681_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_688_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_688_);
v___x_690_ = v___x_666_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
lean_object* v___x_692_; 
lean_del_object(v___x_666_);
lean_inc_ref(v_type_630_);
v___x_692_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_684_, v_type_630_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; size_t v_sz_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc_n(v_a_693_, 2);
lean_dec_ref_known(v___x_692_, 1);
v_sz_694_ = lean_array_size(v_a_693_);
v___x_695_ = ((size_t)0ULL);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_694_, v___x_695_, v_a_693_);
v___x_697_ = l_Array_append___redArg(v_args_633_, v___x_696_);
lean_dec_ref(v___x_696_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 2, v___x_697_);
v___x_699_ = v___x_635_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_declName_631_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_us_632_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v___x_697_);
v___x_699_ = v_reuseFailAlloc_757_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_701_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_684_, v___x_699_, v___x_700_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_fvarId_703_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v_fvarId_703_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_fvarId_703_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 5);
lean_ctor_set(v___x_660_, 0, v_fvarId_703_);
v___x_705_ = v___x_660_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_fvarId_703_);
v___x_705_ = v_reuseFailAlloc_748_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_702_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_708_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_693_, v___x_706_, v___x_707_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_fvarId_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v_fvarId_710_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_fvarId_710_);
lean_inc(v_fvarId_629_);
v___x_711_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_629_, v_fvarId_710_, v_a_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; 
lean_dec_ref_known(v___x_711_, 1);
v___x_712_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_615_, v_a_617_, v_a_620_);
lean_dec_ref(v_letDecl_615_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_723_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_a_709_);
v___x_717_ = v___x_681_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_709_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_709_);
lean_del_object(v___x_681_);
v_a_724_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_712_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_709_);
lean_del_object(v___x_681_);
lean_dec_ref(v_letDecl_615_);
v_a_732_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_711_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_711_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_del_object(v___x_681_);
lean_dec_ref(v_letDecl_615_);
v_a_740_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_708_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_708_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_693_);
lean_del_object(v___x_681_);
lean_del_object(v___x_660_);
lean_dec_ref(v_letDecl_615_);
v_a_749_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_701_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_701_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_del_object(v___x_681_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_758_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_692_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_692_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_del_object(v___x_681_);
lean_dec(v_val_679_);
lean_del_object(v___x_666_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_674_;
}
}
}
else
{
lean_dec(v_a_670_);
lean_del_object(v___x_666_);
lean_dec(v_a_664_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_674_;
}
v___jp_674_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
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
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_666_);
lean_dec(v_a_664_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_768_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_669_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_669_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_777_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_663_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_663_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_787_; 
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_785_ = lean_box(0);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_785_);
v___x_787_ = v___x_656_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_792_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_643_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_643_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v___x_640_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_value_628_);
lean_dec_ref(v_letDecl_615_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* v_letDecl_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t v___x_815_, size_t v_sz_816_, size_t v_i_817_, lean_object* v_bs_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_816_, v_i_817_, v_bs_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* v___x_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_bs_823_){
_start:
{
uint8_t v___x_24447__boxed_824_; size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v___x_24447__boxed_824_ = lean_unbox(v___x_820_);
v_sz_boxed_825_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_826_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24447__boxed_824_, v_sz_boxed_825_, v_i_boxed_826_, v_bs_823_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* v_c_828_, lean_object* v_fvarId_829_, lean_object* v_a_830_){
_start:
{
if (lean_obj_tag(v_c_828_) == 5)
{
lean_object* v_fvarId_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_854_; 
v_fvarId_832_ = lean_ctor_get(v_c_828_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_c_828_);
if (v_isSharedCheck_854_ == 0)
{
v___x_834_ = v_c_828_;
v_isShared_835_ = v_isSharedCheck_854_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_fvarId_832_);
lean_dec(v_c_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_854_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_subst_837_; uint8_t v___x_838_; lean_object* v___x_839_; 
v___x_836_ = lean_st_ref_get(v_a_830_);
v_subst_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref(v_subst_837_);
lean_dec(v___x_836_);
v___x_838_ = 0;
v___x_839_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_837_, v_fvarId_832_, v___x_838_);
lean_dec_ref(v_subst_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_fvarId_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
lean_del_object(v___x_834_);
v_fvarId_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_fvarId_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = l_Lean_instBEqFVarId_beq(v_fvarId_840_, v_fvarId_829_);
lean_dec(v_fvarId_840_);
v___x_845_ = lean_box(v___x_844_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_box(v___x_838_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_850_);
v___x_852_ = v___x_834_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_c_828_);
v___x_855_ = 0;
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* v_c_858_, lean_object* v_fvarId_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_858_, v_fvarId_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec(v_fvarId_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* v_c_863_, lean_object* v_fvarId_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_863_, v_fvarId_864_, v_a_866_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* v_c_874_, lean_object* v_fvarId_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_874_, v_fvarId_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_fvarId_875_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* v_value_885_){
_start:
{
if (lean_obj_tag(v_value_885_) == 4)
{
lean_object* v_fvarId_890_; lean_object* v_args_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_fvarId_890_ = lean_ctor_get(v_value_885_, 0);
v_args_891_ = lean_ctor_get(v_value_885_, 1);
v___x_892_ = lean_array_get_size(v_args_891_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_nat_dec_eq(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
goto v___jp_887_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_inc(v_fvarId_890_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_fvarId_890_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
else
{
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* v_value_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_897_);
lean_dec(v_value_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* v_value_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_900_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* v_value_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_value_910_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* v_a_920_, lean_object* v___x_921_, lean_object* v_fvarId_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_fvarId_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_fvarId_928_ = lean_ctor_get(v_a_920_, 0);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_fvarId_922_);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_921_);
v___x_931_ = lean_array_push(v___x_930_, v___x_929_);
lean_inc(v_fvarId_928_);
v___x_932_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fvarId_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* v_a_934_, lean_object* v___x_935_, lean_object* v_fvarId_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_934_, v___x_935_, v_fvarId_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___x_935_);
lean_dec_ref(v_a_934_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t v_pu_943_, uint8_t v_t_944_, lean_object* v_args_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_subst_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_948_ = lean_st_ref_get(v___y_946_);
v_subst_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_subst_949_);
lean_dec(v___x_948_);
v___x_950_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_943_, v_subst_949_, v_args_945_, v_t_944_);
lean_dec_ref(v_subst_949_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* v_pu_952_, lean_object* v_t_953_, lean_object* v_args_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
uint8_t v_pu_boxed_957_; uint8_t v_t_boxed_958_; lean_object* v_res_959_; 
v_pu_boxed_957_ = lean_unbox(v_pu_952_);
v_t_boxed_958_ = lean_unbox(v_t_953_);
v_res_959_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_boxed_957_, v_t_boxed_958_, v_args_954_, v___y_955_);
lean_dec(v___y_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* v_as_960_, size_t v_i_961_, size_t v_stop_962_, lean_object* v_b_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_eq(v_i_961_, v_stop_962_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_array_uget_borrowed(v_as_960_, v_i_961_);
lean_inc(v___x_967_);
v___x_968_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_967_, v___y_964_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; size_t v___x_970_; size_t v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_961_, v___x_970_);
v_i_961_ = v___x_971_;
v_b_963_ = v_a_969_;
goto _start;
}
else
{
return v___x_968_;
}
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_b_963_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* v_as_974_, lean_object* v_i_975_, lean_object* v_stop_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
size_t v_i_boxed_980_; size_t v_stop_boxed_981_; lean_object* v_res_982_; 
v_i_boxed_980_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_stop_boxed_981_ = lean_unbox_usize(v_stop_976_);
lean_dec(v_stop_976_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_974_, v_i_boxed_980_, v_stop_boxed_981_, v_b_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v_as_974_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v_as_983_, size_t v_i_984_, size_t v_stop_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = lean_usize_dec_eq(v_i_984_, v_stop_985_);
if (v___x_986_ == 0)
{
uint8_t v___x_987_; lean_object* v___y_989_; lean_object* v___x_993_; 
v___x_987_ = 1;
v___x_993_ = lean_array_uget_borrowed(v_as_983_, v_i_984_);
switch(lean_obj_tag(v___x_993_))
{
case 0:
{
lean_object* v_code_994_; 
v_code_994_ = lean_ctor_get(v___x_993_, 2);
v___y_989_ = v_code_994_;
goto v___jp_988_;
}
case 1:
{
lean_object* v_code_995_; 
v_code_995_ = lean_ctor_get(v___x_993_, 1);
v___y_989_ = v_code_995_;
goto v___jp_988_;
}
default: 
{
lean_object* v_code_996_; 
v_code_996_ = lean_ctor_get(v___x_993_, 0);
v___y_989_ = v_code_996_;
goto v___jp_988_;
}
}
v___jp_988_:
{
if (lean_obj_tag(v___y_989_) == 6)
{
if (v___x_986_ == 0)
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_984_, v___x_990_);
v_i_984_ = v___x_991_;
goto _start;
}
else
{
return v___x_987_;
}
}
else
{
return v___x_987_;
}
}
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_){
_start:
{
size_t v_i_boxed_1001_; size_t v_stop_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_i_boxed_1001_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1002_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_998_, v_i_boxed_1001_, v_stop_boxed_1002_);
lean_dec_ref(v_as_998_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1005_, uint8_t v_t_1006_, lean_object* v_i_1007_, lean_object* v_as_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = lean_array_get_size(v_as_1008_);
v___x_1013_ = lean_nat_dec_lt(v_i_1007_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v_i_1007_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_as_1008_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v_type_1016_; lean_object* v___x_1017_; lean_object* v_subst_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1015_ = lean_array_fget_borrowed(v_as_1008_, v_i_1007_);
v_type_1016_ = lean_ctor_get(v_a_1015_, 2);
v___x_1017_ = lean_st_ref_get(v___y_1009_);
v_subst_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_subst_1018_);
lean_dec(v___x_1017_);
lean_inc_ref(v_type_1016_);
v___x_1019_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1005_, v_subst_1018_, v_t_1006_, v_type_1016_);
lean_dec_ref(v_subst_1018_);
lean_inc(v_a_1015_);
v___x_1020_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1005_, v_a_1015_, v___x_1019_, v___y_1010_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; size_t v___x_1022_; size_t v___x_1023_; uint8_t v___x_1024_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = lean_ptr_addr(v_a_1015_);
v___x_1023_ = lean_ptr_addr(v_a_1021_);
v___x_1024_ = lean_usize_dec_eq(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_add(v_i_1007_, v___x_1025_);
v___x_1027_ = lean_array_fset(v_as_1008_, v_i_1007_, v_a_1021_);
lean_dec(v_i_1007_);
v_i_1007_ = v___x_1026_;
v_as_1008_ = v___x_1027_;
goto _start;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v_a_1021_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_i_1007_, v___x_1029_);
lean_dec(v_i_1007_);
v_i_1007_ = v___x_1030_;
goto _start;
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_as_1008_);
lean_dec(v_i_1007_);
v_a_1032_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1020_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1020_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1040_, lean_object* v_t_1041_, lean_object* v_i_1042_, lean_object* v_as_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_pu_boxed_1047_; uint8_t v_t_boxed_1048_; lean_object* v_res_1049_; 
v_pu_boxed_1047_ = lean_unbox(v_pu_1040_);
v_t_boxed_1048_ = lean_unbox(v_t_1041_);
v_res_1049_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1047_, v_t_boxed_1048_, v_i_1042_, v_as_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1050_, uint8_t v_t_1051_, lean_object* v_ps_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1050_, v_t_1051_, v___x_1061_, v_ps_1052_, v___y_1054_, v___y_1057_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1063_, lean_object* v_t_1064_, lean_object* v_ps_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v_pu_boxed_1074_; uint8_t v_t_boxed_1075_; lean_object* v_res_1076_; 
v_pu_boxed_1074_ = lean_unbox(v_pu_1063_);
v_t_boxed_1075_ = lean_unbox(v_t_1064_);
v_res_1076_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1074_, v_t_boxed_1075_, v_ps_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1077_, uint8_t v_t_1078_, lean_object* v_decl_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_type_1083_; lean_object* v_value_1084_; lean_object* v___x_1085_; lean_object* v_subst_1086_; lean_object* v___x_1087_; lean_object* v_subst_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_type_1083_ = lean_ctor_get(v_decl_1079_, 2);
v_value_1084_ = lean_ctor_get(v_decl_1079_, 3);
v___x_1085_ = lean_st_ref_get(v___y_1080_);
v_subst_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_subst_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_st_ref_get(v___y_1080_);
v_subst_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_subst_1088_);
lean_dec(v___x_1087_);
lean_inc_ref(v_type_1083_);
v___x_1089_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1077_, v_subst_1086_, v_t_1078_, v_type_1083_);
lean_dec_ref(v_subst_1086_);
lean_inc(v_value_1084_);
v___x_1090_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1077_, v_subst_1088_, v_value_1084_, v_t_1078_);
lean_dec_ref(v_subst_1088_);
v___x_1091_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1077_, v_decl_1079_, v___x_1089_, v___x_1090_, v___y_1081_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1092_, lean_object* v_t_1093_, lean_object* v_decl_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_pu_boxed_1098_; uint8_t v_t_boxed_1099_; lean_object* v_res_1100_; 
v_pu_boxed_1098_ = lean_unbox(v_pu_1092_);
v_t_boxed_1099_ = lean_unbox(v_t_1093_);
v_res_1100_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1098_, v_t_boxed_1099_, v_decl_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec(v___y_1095_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1101_, lean_object* v___f_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v_fvarId_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
lean_inc(v_fvarId_1105_);
v___x_1111_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1105_, v___y_1101_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1111_, 1);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1103_);
v___x_1112_ = lean_apply_9(v___f_1102_, v_fvarId_1105_, v___y_1103_, v___y_1101_, v___y_1104_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, lean_box(0));
return v___x_1112_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_fvarId_1105_);
lean_dec_ref(v___f_1102_);
v_a_1113_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1111_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1121_, lean_object* v___f_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v_fvarId_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1121_, v___f_1122_, v___y_1123_, v___y_1124_, v_fvarId_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1121_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v_ks_1136_; lean_object* v_vs_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_ks_1136_ = lean_ctor_get(v_x_1132_, 0);
v_vs_1137_ = lean_ctor_get(v_x_1132_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v_x_1132_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_vs_1137_);
lean_inc(v_ks_1136_);
lean_dec(v_x_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_get_size(v_ks_1136_);
v___x_1142_ = lean_nat_dec_lt(v_x_1133_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_dec(v_x_1133_);
v___x_1143_ = lean_array_push(v_ks_1136_, v_x_1134_);
v___x_1144_ = lean_array_push(v_vs_1137_, v_x_1135_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1144_);
lean_ctor_set(v___x_1139_, 0, v___x_1143_);
v___x_1146_ = v___x_1139_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
lean_object* v_k_x27_1148_; uint8_t v___x_1149_; 
v_k_x27_1148_ = lean_array_fget_borrowed(v_ks_1136_, v_x_1133_);
v___x_1149_ = lean_name_eq(v_x_1134_, v_k_x27_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1151_; 
if (v_isShared_1140_ == 0)
{
v___x_1151_ = v___x_1139_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_ks_1136_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_vs_1137_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_x_1133_, v___x_1152_);
lean_dec(v_x_1133_);
v_x_1132_ = v___x_1151_;
v_x_1133_ = v___x_1153_;
goto _start;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_array_fset(v_ks_1136_, v_x_1133_, v_x_1134_);
v___x_1157_ = lean_array_fset(v_vs_1137_, v_x_1133_, v_x_1135_);
lean_dec(v_x_1133_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1157_);
lean_ctor_set(v___x_1139_, 0, v___x_1156_);
v___x_1159_ = v___x_1139_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1162_, lean_object* v_k_1163_, lean_object* v_v_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1162_, v___x_1165_, v_k_1163_, v_v_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1168_, size_t v_x_1169_, size_t v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_es_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v_j_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_es_1173_ = lean_ctor_get(v_x_1168_, 0);
v___x_1174_ = ((size_t)31ULL);
v___x_1175_ = lean_usize_land(v_x_1169_, v___x_1174_);
v_j_1176_ = lean_usize_to_nat(v___x_1175_);
v___x_1177_ = lean_array_get_size(v_es_1173_);
v___x_1178_ = lean_nat_dec_lt(v_j_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_j_1176_);
lean_dec(v_x_1172_);
lean_dec(v_x_1171_);
return v_x_1168_;
}
else
{
lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1217_; 
lean_inc_ref(v_es_1173_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_x_1168_, 0);
lean_dec(v_unused_1218_);
v___x_1180_ = v_x_1168_;
v_isShared_1181_ = v_isSharedCheck_1217_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_x_1168_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1217_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_v_1182_; lean_object* v___x_1183_; lean_object* v_xs_x27_1184_; lean_object* v___y_1186_; 
v_v_1182_ = lean_array_fget(v_es_1173_, v_j_1176_);
v___x_1183_ = lean_box(0);
v_xs_x27_1184_ = lean_array_fset(v_es_1173_, v_j_1176_, v___x_1183_);
switch(lean_obj_tag(v_v_1182_))
{
case 0:
{
lean_object* v_key_1191_; lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_key_1191_ = lean_ctor_get(v_v_1182_, 0);
v_val_1192_ = lean_ctor_get(v_v_1182_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_v_1182_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v_v_1182_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_inc(v_key_1191_);
lean_dec(v_v_1182_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_name_eq(v_x_1171_, v_key_1191_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_del_object(v___x_1194_);
v___x_1197_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1191_, v_val_1192_, v_x_1171_, v_x_1172_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
v___y_1186_ = v___x_1198_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1200_; 
lean_dec(v_val_1192_);
lean_dec(v_key_1191_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_x_1172_);
lean_ctor_set(v___x_1194_, 0, v_x_1171_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_x_1171_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_x_1172_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v___y_1186_ = v___x_1200_;
goto v___jp_1185_;
}
}
}
}
case 1:
{
lean_object* v_node_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1215_; 
v_node_1203_ = lean_ctor_get(v_v_1182_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_v_1182_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1205_ = v_v_1182_;
v_isShared_1206_ = v_isSharedCheck_1215_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_node_1203_);
lean_dec(v_v_1182_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1215_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1207_ = ((size_t)5ULL);
v___x_1208_ = lean_usize_shift_right(v_x_1169_, v___x_1207_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_add(v_x_1170_, v___x_1209_);
v___x_1211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1203_, v___x_1208_, v___x_1210_, v_x_1171_, v_x_1172_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1211_);
v___x_1213_ = v___x_1205_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
v___y_1186_ = v___x_1213_;
goto v___jp_1185_;
}
}
}
default: 
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_x_1171_);
lean_ctor_set(v___x_1216_, 1, v_x_1172_);
v___y_1186_ = v___x_1216_;
goto v___jp_1185_;
}
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_array_fset(v_xs_x27_1184_, v_j_1176_, v___y_1186_);
lean_dec(v_j_1176_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1187_);
v___x_1189_ = v___x_1180_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_ks_1219_; lean_object* v_vs_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1240_; 
v_ks_1219_ = lean_ctor_get(v_x_1168_, 0);
v_vs_1220_ = lean_ctor_get(v_x_1168_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1222_ = v_x_1168_;
v_isShared_1223_ = v_isSharedCheck_1240_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_vs_1220_);
lean_inc(v_ks_1219_);
lean_dec(v_x_1168_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1240_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_ks_1219_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_vs_1220_);
v___x_1225_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v_newNode_1226_; uint8_t v___y_1228_; size_t v___x_1234_; uint8_t v___x_1235_; 
v_newNode_1226_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1225_, v_x_1171_, v_x_1172_);
v___x_1234_ = ((size_t)7ULL);
v___x_1235_ = lean_usize_dec_le(v___x_1234_, v_x_1170_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1226_);
v___x_1237_ = lean_unsigned_to_nat(4u);
v___x_1238_ = lean_nat_dec_lt(v___x_1236_, v___x_1237_);
lean_dec(v___x_1236_);
v___y_1228_ = v___x_1238_;
goto v___jp_1227_;
}
else
{
v___y_1228_ = v___x_1235_;
goto v___jp_1227_;
}
v___jp_1227_:
{
if (v___y_1228_ == 0)
{
lean_object* v_ks_1229_; lean_object* v_vs_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_ks_1229_ = lean_ctor_get(v_newNode_1226_, 0);
lean_inc_ref(v_ks_1229_);
v_vs_1230_ = lean_ctor_get(v_newNode_1226_, 1);
lean_inc_ref(v_vs_1230_);
lean_dec_ref(v_newNode_1226_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1170_, v_ks_1229_, v_vs_1230_, v___x_1231_, v___x_1232_);
lean_dec_ref(v_vs_1230_);
lean_dec_ref(v_ks_1229_);
return v___x_1233_;
}
else
{
return v_newNode_1226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1241_, lean_object* v_keys_1242_, lean_object* v_vals_1243_, lean_object* v_i_1244_, lean_object* v_entries_1245_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_array_get_size(v_keys_1242_);
v___x_1247_ = lean_nat_dec_lt(v_i_1244_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v_i_1244_);
return v_entries_1245_;
}
else
{
lean_object* v_k_1248_; lean_object* v_v_1249_; uint64_t v___y_1251_; 
v_k_1248_ = lean_array_fget_borrowed(v_keys_1242_, v_i_1244_);
v_v_1249_ = lean_array_fget_borrowed(v_vals_1243_, v_i_1244_);
if (lean_obj_tag(v_k_1248_) == 0)
{
uint64_t v___x_1262_; 
v___x_1262_ = 1723ULL;
v___y_1251_ = v___x_1262_;
goto v___jp_1250_;
}
else
{
uint64_t v_hash_1263_; 
v_hash_1263_ = lean_ctor_get_uint64(v_k_1248_, sizeof(void*)*2);
v___y_1251_ = v_hash_1263_;
goto v___jp_1250_;
}
v___jp_1250_:
{
size_t v_h_1252_; size_t v___x_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v_h_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_h_1252_ = lean_uint64_to_usize(v___y_1251_);
v___x_1253_ = ((size_t)5ULL);
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_sub(v_depth_1241_, v___x_1255_);
v___x_1257_ = lean_usize_mul(v___x_1253_, v___x_1256_);
v_h_1258_ = lean_usize_shift_right(v_h_1252_, v___x_1257_);
v___x_1259_ = lean_nat_add(v_i_1244_, v___x_1254_);
lean_dec(v_i_1244_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
v___x_1260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1245_, v_h_1258_, v_depth_1241_, v_k_1248_, v_v_1249_);
v_i_1244_ = v___x_1259_;
v_entries_1245_ = v___x_1260_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1264_, lean_object* v_keys_1265_, lean_object* v_vals_1266_, lean_object* v_i_1267_, lean_object* v_entries_1268_){
_start:
{
size_t v_depth_boxed_1269_; lean_object* v_res_1270_; 
v_depth_boxed_1269_ = lean_unbox_usize(v_depth_1264_);
lean_dec(v_depth_1264_);
v_res_1270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1269_, v_keys_1265_, v_vals_1266_, v_i_1267_, v_entries_1268_);
lean_dec_ref(v_vals_1266_);
lean_dec_ref(v_keys_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
size_t v_x_47236__boxed_1276_; size_t v_x_47237__boxed_1277_; lean_object* v_res_1278_; 
v_x_47236__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_x_47237__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1271_, v_x_47236__boxed_1276_, v_x_47237__boxed_1277_, v_x_1274_, v_x_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
uint64_t v___y_1283_; 
if (lean_obj_tag(v_x_1280_) == 0)
{
uint64_t v___x_1287_; 
v___x_1287_ = 1723ULL;
v___y_1283_ = v___x_1287_;
goto v___jp_1282_;
}
else
{
uint64_t v_hash_1288_; 
v_hash_1288_ = lean_ctor_get_uint64(v_x_1280_, sizeof(void*)*2);
v___y_1283_ = v_hash_1288_;
goto v___jp_1282_;
}
v___jp_1282_:
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_uint64_to_usize(v___y_1283_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1279_, v___x_1284_, v___x_1285_, v_x_1280_, v_x_1281_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1289_, lean_object* v_b_1290_){
_start:
{
lean_object* v_array_1291_; lean_object* v_start_1292_; lean_object* v_stop_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1306_; 
v_array_1291_ = lean_ctor_get(v_a_1289_, 0);
v_start_1292_ = lean_ctor_get(v_a_1289_, 1);
v_stop_1293_ = lean_ctor_get(v_a_1289_, 2);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1295_ = v_a_1289_;
v_isShared_1296_ = v_isSharedCheck_1306_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_stop_1293_);
lean_inc(v_start_1292_);
lean_inc(v_array_1291_);
lean_dec(v_a_1289_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1306_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_lt(v_start_1292_, v_stop_1293_);
if (v___x_1297_ == 0)
{
lean_del_object(v___x_1295_);
lean_dec(v_stop_1293_);
lean_dec(v_start_1292_);
lean_dec_ref(v_array_1291_);
return v_b_1290_;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_add(v_start_1292_, v___x_1298_);
lean_inc_ref(v_array_1291_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v___x_1299_);
v___x_1301_ = v___x_1295_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_array_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_stop_1293_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_array_fget(v_array_1291_, v_start_1292_);
lean_dec(v_start_1292_);
lean_dec_ref(v_array_1291_);
v___x_1303_ = lean_array_push(v_b_1290_, v___x_1302_);
v_a_1289_ = v___x_1301_;
v_b_1290_ = v___x_1303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_b_1310_);
return v___x_1314_;
}
else
{
lean_object* v_array_1315_; lean_object* v_start_1316_; lean_object* v_stop_1317_; uint8_t v___x_1318_; 
v_array_1315_ = lean_ctor_get(v_b_1310_, 0);
v_start_1316_ = lean_ctor_get(v_b_1310_, 1);
v_stop_1317_ = lean_ctor_get(v_b_1310_, 2);
v___x_1318_ = lean_nat_dec_lt(v_start_1316_, v_stop_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_b_1310_);
return v___x_1319_;
}
else
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1352_; 
lean_inc(v_stop_1317_);
lean_inc(v_start_1316_);
lean_inc_ref(v_array_1315_);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_b_1310_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1353_ = lean_ctor_get(v_b_1310_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_b_1310_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_b_1310_, 0);
lean_dec(v_unused_1355_);
v___x_1321_ = v_b_1310_;
v_isShared_1322_ = v_isSharedCheck_1352_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v_b_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1352_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v_fvarId_1325_; lean_object* v_subst_1326_; lean_object* v_used_1327_; lean_object* v_binderRenaming_1328_; lean_object* v_funDeclInfoMap_1329_; uint8_t v_simplified_1330_; lean_object* v_visited_1331_; lean_object* v_inline_1332_; lean_object* v_inlineLocal_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1351_; 
v___x_1323_ = lean_st_ref_take(v___y_1311_);
v_a_1324_ = lean_array_uget_borrowed(v_as_1307_, v_i_1309_);
v_fvarId_1325_ = lean_ctor_get(v_a_1324_, 0);
v_subst_1326_ = lean_ctor_get(v___x_1323_, 0);
v_used_1327_ = lean_ctor_get(v___x_1323_, 1);
v_binderRenaming_1328_ = lean_ctor_get(v___x_1323_, 2);
v_funDeclInfoMap_1329_ = lean_ctor_get(v___x_1323_, 3);
v_simplified_1330_ = lean_ctor_get_uint8(v___x_1323_, sizeof(void*)*7);
v_visited_1331_ = lean_ctor_get(v___x_1323_, 4);
v_inline_1332_ = lean_ctor_get(v___x_1323_, 5);
v_inlineLocal_1333_ = lean_ctor_get(v___x_1323_, 6);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1335_ = v___x_1323_;
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_inlineLocal_1333_);
lean_inc(v_inline_1332_);
lean_inc(v_visited_1331_);
lean_inc(v_funDeclInfoMap_1329_);
lean_inc(v_binderRenaming_1328_);
lean_inc(v_used_1327_);
lean_inc(v_subst_1326_);
lean_dec(v___x_1323_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = lean_array_fget_borrowed(v_array_1315_, v_start_1316_);
lean_inc(v___x_1337_);
lean_inc(v_fvarId_1325_);
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1326_, v_fvarId_1325_, v___x_1337_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_used_1327_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_binderRenaming_1328_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_funDeclInfoMap_1329_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_visited_1331_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_inline_1332_);
lean_ctor_set(v_reuseFailAlloc_1350_, 6, v_inlineLocal_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*7, v_simplified_1330_);
v___x_1340_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1341_ = lean_st_ref_set(v___y_1311_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_add(v_start_1316_, v___x_1342_);
lean_dec(v_start_1316_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1343_);
v___x_1345_ = v___x_1321_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_array_1315_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_stop_1317_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
size_t v___x_1346_; size_t v___x_1347_; 
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1309_, v___x_1346_);
v_i_1309_ = v___x_1347_;
v_b_1310_ = v___x_1345_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1356_, lean_object* v_sz_1357_, lean_object* v_i_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
size_t v_sz_boxed_1362_; size_t v_i_boxed_1363_; lean_object* v_res_1364_; 
v_sz_boxed_1362_ = lean_unbox_usize(v_sz_1357_);
lean_dec(v_sz_1357_);
v_i_boxed_1363_ = lean_unbox_usize(v_i_1358_);
lean_dec(v_i_1358_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1356_, v_sz_boxed_1362_, v_i_boxed_1363_, v_b_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v_as_1356_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1365_, size_t v_i_1366_, size_t v_stop_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_eq(v_i_1366_, v_stop_1367_);
if (v___x_1371_ == 0)
{
uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = 0;
v___x_1373_ = lean_array_uget_borrowed(v_as_1365_, v_i_1366_);
v___x_1374_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1372_, v___x_1373_, v___y_1369_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; size_t v___x_1376_; size_t v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1366_, v___x_1376_);
v_i_1366_ = v___x_1377_;
v_b_1368_ = v_a_1375_;
goto _start;
}
else
{
return v___x_1374_;
}
}
else
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1368_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1380_, lean_object* v_i_1381_, lean_object* v_stop_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
size_t v_i_boxed_1386_; size_t v_stop_boxed_1387_; lean_object* v_res_1388_; 
v_i_boxed_1386_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_stop_boxed_1387_ = lean_unbox_usize(v_stop_1382_);
lean_dec(v_stop_1382_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1380_, v_i_boxed_1386_, v_stop_boxed_1387_, v_b_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v_as_1380_);
return v_res_1388_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = 0;
v___x_1390_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1393_ = lean_panic_fn_borrowed(v___x_1392_, v_msg_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1394_, size_t v_i_1395_, size_t v_stop_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_eq(v_i_1395_, v_stop_1396_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v_type_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_array_uget_borrowed(v_as_1394_, v_i_1395_);
v_type_1401_ = lean_ctor_get(v___x_1400_, 2);
v___x_1402_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1401_, v___y_1397_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_unbox(v_a_1403_);
if (v___x_1407_ == 0)
{
size_t v___x_1408_; size_t v___x_1409_; 
lean_del_object(v___x_1405_);
lean_dec(v_a_1403_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1395_, v___x_1408_);
v_i_1395_ = v___x_1409_;
goto _start;
}
else
{
lean_object* v___x_1412_; 
if (v_isShared_1406_ == 0)
{
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1403_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
return v___x_1402_;
}
}
else
{
uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = 0;
v___x_1416_ = lean_box(v___x_1415_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1418_, lean_object* v_i_1419_, lean_object* v_stop_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
size_t v_i_boxed_1423_; size_t v_stop_boxed_1424_; lean_object* v_res_1425_; 
v_i_boxed_1423_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_stop_boxed_1424_ = lean_unbox_usize(v_stop_1420_);
lean_dec(v_stop_1420_);
v_res_1425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1418_, v_i_boxed_1423_, v_stop_boxed_1424_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v_as_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1426_, size_t v_i_1427_, size_t v_stop_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_usize_dec_eq(v_i_1427_, v_stop_1428_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = 0;
v___x_1434_ = lean_array_uget_borrowed(v_as_1426_, v_i_1427_);
v___x_1435_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1433_, v___x_1434_, v___y_1430_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; size_t v___x_1437_; size_t v___x_1438_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_add(v_i_1427_, v___x_1437_);
v_i_1427_ = v___x_1438_;
v_b_1429_ = v_a_1436_;
goto _start;
}
else
{
return v___x_1435_;
}
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_b_1429_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1441_, lean_object* v_i_1442_, lean_object* v_stop_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
size_t v_i_boxed_1447_; size_t v_stop_boxed_1448_; lean_object* v_res_1449_; 
v_i_boxed_1447_ = lean_unbox_usize(v_i_1442_);
lean_dec(v_i_1442_);
v_stop_boxed_1448_ = lean_unbox_usize(v_stop_1443_);
lean_dec(v_stop_1443_);
v_res_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1441_, v_i_boxed_1447_, v_stop_boxed_1448_, v_b_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v_as_1441_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1450_, size_t v_i_1451_, size_t v_stop_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_a_1460_; lean_object* v___y_1465_; uint8_t v___x_1467_; 
v___x_1467_ = lean_usize_dec_eq(v_i_1451_, v_stop_1452_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_array_uget_borrowed(v_as_1450_, v_i_1451_);
v___x_1470_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1469_);
v___x_1471_ = lean_array_get_size(v___x_1470_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_nat_dec_lt(v___x_1468_, v___x_1471_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v___x_1470_);
v_a_1460_ = v___x_1472_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_nat_dec_le(v___x_1471_, v___x_1471_);
if (v___x_1474_ == 0)
{
if (v___x_1473_ == 0)
{
lean_dec_ref(v___x_1470_);
v_a_1460_ = v___x_1472_;
goto v___jp_1459_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = lean_usize_of_nat(v___x_1471_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1470_, v___x_1475_, v___x_1476_, v___x_1472_, v___y_1455_);
lean_dec_ref(v___x_1470_);
v___y_1465_ = v___x_1477_;
goto v___jp_1464_;
}
}
else
{
size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = lean_usize_of_nat(v___x_1471_);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1470_, v___x_1478_, v___x_1479_, v___x_1472_, v___y_1455_);
lean_dec_ref(v___x_1470_);
v___y_1465_ = v___x_1480_;
goto v___jp_1464_;
}
}
}
else
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_b_1453_);
return v___x_1481_;
}
v___jp_1459_:
{
size_t v___x_1461_; size_t v___x_1462_; 
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_add(v_i_1451_, v___x_1461_);
v_i_1451_ = v___x_1462_;
v_b_1453_ = v_a_1460_;
goto _start;
}
v___jp_1464_:
{
if (lean_obj_tag(v___y_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___y_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___y_1465_, 1);
v_a_1460_ = v_a_1466_;
goto v___jp_1459_;
}
else
{
return v___y_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1482_, lean_object* v_i_1483_, lean_object* v_stop_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
size_t v_i_boxed_1491_; size_t v_stop_boxed_1492_; lean_object* v_res_1493_; 
v_i_boxed_1491_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_stop_boxed_1492_ = lean_unbox_usize(v_stop_1484_);
lean_dec(v_stop_1484_);
v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1482_, v_i_boxed_1491_, v_stop_boxed_1492_, v_b_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec_ref(v_as_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1494_, size_t v_i_1495_, size_t v_stop_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_eq(v_i_1495_, v_stop_1496_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v_fvarId_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_array_uget_borrowed(v_as_1494_, v_i_1495_);
v_fvarId_1501_ = lean_ctor_get(v___x_1500_, 0);
v___x_1502_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1501_, v___y_1497_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1514_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1514_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1514_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_unbox(v_a_1503_);
if (v___x_1507_ == 0)
{
size_t v___x_1508_; size_t v___x_1509_; 
lean_del_object(v___x_1505_);
lean_dec(v_a_1503_);
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_add(v_i_1495_, v___x_1508_);
v_i_1495_ = v___x_1509_;
goto _start;
}
else
{
lean_object* v___x_1512_; 
if (v_isShared_1506_ == 0)
{
v___x_1512_ = v___x_1505_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1503_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
return v___x_1502_;
}
}
else
{
uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = 0;
v___x_1516_ = lean_box(v___x_1515_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1518_, lean_object* v_i_1519_, lean_object* v_stop_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
size_t v_i_boxed_1523_; size_t v_stop_boxed_1524_; lean_object* v_res_1525_; 
v_i_boxed_1523_ = lean_unbox_usize(v_i_1519_);
lean_dec(v_i_1519_);
v_stop_boxed_1524_ = lean_unbox_usize(v_stop_1520_);
lean_dec(v_stop_1520_);
v_res_1525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1518_, v_i_boxed_1523_, v_stop_boxed_1524_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v_as_1518_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1530_ = lean_unsigned_to_nat(9u);
v___x_1531_ = lean_unsigned_to_nat(641u);
v___x_1532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1533_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1534_ = l_mkPanicMessageWithDecl(v___x_1533_, v___x_1532_, v___x_1531_, v___x_1530_, v___x_1529_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v_fvarId_1540_, lean_object* v_k_1541_, lean_object* v_args_1542_, uint8_t v___x_1543_, lean_object* v___x_1544_, lean_object* v_result_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_lower_1555_; lean_object* v_upper_1556_; uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec(v___x_1544_);
lean_dec_ref(v_args_1542_);
lean_dec(v___x_1539_);
lean_dec(v___x_1538_);
v___x_1584_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1540_, v_result_1545_, v___y_1547_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1584_, 1);
lean_inc_ref(v___y_1551_);
v___x_1585_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1541_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1585_;
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_k_1541_);
v_a_1586_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1584_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_le(v___x_1538_, v___x_1544_);
if (v___x_1594_ == 0)
{
lean_dec(v___x_1544_);
v_lower_1555_ = v___x_1538_;
v_upper_1556_ = v___x_1539_;
goto v___jp_1554_;
}
else
{
lean_dec(v___x_1538_);
v_lower_1555_ = v___x_1544_;
v_upper_1556_ = v___x_1539_;
goto v___jp_1554_;
}
}
v___jp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1557_ = l_Array_toSubarray___redArg(v_args_1542_, v_lower_1555_, v_upper_1556_);
v___x_1558_ = l_Subarray_copy___redArg(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_result_1545_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1561_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1543_, v___x_1559_, v___x_1560_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_fvarId_1563_; lean_object* v___x_1564_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_fvarId_1563_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_fvarId_1563_);
v___x_1564_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1540_, v_fvarId_1563_, v___y_1547_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref_known(v___x_1564_, 1);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1562_);
lean_ctor_set(v___x_1565_, 1, v_k_1541_);
lean_inc_ref(v___y_1551_);
v___x_1566_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1565_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1566_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1562_);
lean_dec_ref(v_k_1541_);
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
lean_dec_ref(v_k_1541_);
lean_dec(v_fvarId_1540_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_fvarId_1597_, lean_object* v_k_1598_, lean_object* v_args_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_result_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v___x_47756__boxed_1611_; lean_object* v_res_1612_; 
v___x_47756__boxed_1611_ = lean_unbox(v___x_1600_);
v_res_1612_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1595_, v___x_1596_, v_fvarId_1597_, v_k_1598_, v_args_1599_, v___x_47756__boxed_1611_, v___x_1601_, v_result_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1613_, lean_object* v_k_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_fvarId_1623_; lean_object* v_value_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1962_; 
v_fvarId_1623_ = lean_ctor_get(v_letDecl_1613_, 0);
v_value_1624_ = lean_ctor_get(v_letDecl_1613_, 3);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_letDecl_1613_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; lean_object* v_unused_1964_; 
v_unused_1963_ = lean_ctor_get(v_letDecl_1613_, 2);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_letDecl_1613_, 1);
lean_dec(v_unused_1964_);
v___x_1626_ = v_letDecl_1613_;
v_isShared_1627_ = v_isSharedCheck_1962_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_value_1624_);
lean_inc(v_fvarId_1623_);
lean_dec(v_letDecl_1613_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1962_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; 
lean_inc(v_value_1624_);
v___x_1628_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1624_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1953_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1953_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1953_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_a_1629_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1631_);
v_val_1633_ = lean_ctor_get(v_a_1629_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1635_ = v_a_1629_;
v_isShared_1636_ = v_isSharedCheck_1948_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_val_1633_);
lean_dec(v_a_1629_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1948_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_params_1637_; lean_object* v_value_1638_; lean_object* v_fType_1639_; lean_object* v_args_1640_; uint8_t v_recursive_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; 
v_params_1637_ = lean_ctor_get(v_val_1633_, 0);
v_value_1638_ = lean_ctor_get(v_val_1633_, 1);
v_fType_1639_ = lean_ctor_get(v_val_1633_, 2);
v_args_1640_ = lean_ctor_get(v_val_1633_, 3);
v_recursive_1641_ = lean_ctor_get_uint8(v_val_1633_, sizeof(void*)*4 + 2);
v___x_1642_ = lean_array_get_size(v_args_1640_);
v___x_1643_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1633_);
v___x_1644_ = lean_nat_dec_lt(v___x_1642_, v___x_1643_);
if (lean_obj_tag(v_value_1624_) == 3)
{
lean_object* v_declName_1928_; lean_object* v___x_1929_; 
v_declName_1928_ = lean_ctor_get(v_value_1624_, 0);
lean_inc_n(v_declName_1928_, 2);
lean_dec_ref_known(v_value_1624_, 3);
v___x_1929_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1641_, v_declName_1928_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v_declName_1931_; lean_object* v_config_1932_; lean_object* v_inlineStack_1933_; lean_object* v_inlineStackOccs_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v_declName_1931_ = lean_ctor_get(v_a_1615_, 0);
v_config_1932_ = lean_ctor_get(v_a_1615_, 1);
v_inlineStack_1933_ = lean_ctor_get(v_a_1615_, 2);
v_inlineStackOccs_1934_ = lean_ctor_get(v_a_1615_, 3);
lean_inc(v_inlineStack_1933_);
lean_inc(v_declName_1928_);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_declName_1928_);
lean_ctor_set(v___x_1935_, 1, v_inlineStack_1933_);
lean_inc_ref(v_inlineStackOccs_1934_);
v___x_1936_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1934_, v_declName_1928_, v_a_1930_);
lean_inc_ref(v_config_1932_);
lean_inc(v_declName_1931_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 3, v___x_1936_);
lean_ctor_set(v___x_1626_, 2, v___x_1935_);
lean_ctor_set(v___x_1626_, 1, v_config_1932_);
lean_ctor_set(v___x_1626_, 0, v_declName_1931_);
v___x_1938_ = v___x_1626_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_declName_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_config_1932_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
v___y_1827_ = v___x_1938_;
v___y_1828_ = v_a_1616_;
v___y_1829_ = v_a_1617_;
v___y_1830_ = v_a_1618_;
v___y_1831_ = v_a_1619_;
v___y_1832_ = v_a_1620_;
v___y_1833_ = v_a_1621_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_declName_1928_);
lean_dec(v___x_1643_);
lean_del_object(v___x_1635_);
lean_dec(v_val_1633_);
lean_del_object(v___x_1626_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
v_a_1940_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1929_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1929_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_del_object(v___x_1626_);
lean_dec(v_value_1624_);
lean_inc_ref(v_a_1615_);
v___y_1827_ = v_a_1615_;
v___y_1828_ = v_a_1616_;
v___y_1829_ = v_a_1617_;
v___y_1830_ = v_a_1618_;
v___y_1831_ = v_a_1619_;
v___y_1832_ = v_a_1620_;
v___y_1833_ = v_a_1621_;
goto v___jp_1826_;
}
v___jp_1645_:
{
lean_object* v___x_1659_; 
lean_inc_ref(v___y_1647_);
v___x_1659_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1651_, v___y_1649_, v___y_1658_, v___y_1648_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1658_);
if (lean_obj_tag(v___x_1661_) == 0)
{
uint8_t v___x_1662_; 
lean_dec_ref_known(v___x_1661_, 1);
v___x_1662_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1660_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v___y_1657_);
v___x_1663_ = lean_mk_empty_array_with_capacity(v___y_1656_);
lean_dec(v___y_1656_);
lean_inc_ref(v___x_1663_);
v___x_1664_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1652_, v___x_1663_);
v___x_1665_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1653_, v_fType_1639_, v___x_1664_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc_n(v_a_1666_, 2);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l_Lean_Expr_headBeta(v_a_1666_);
v___x_1668_ = l_Lean_Expr_isForall(v___x_1667_);
lean_dec_ref(v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref(v___x_1663_);
v___x_1669_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1653_, v_a_1666_, v___x_1644_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v_fvarId_1671_; lean_object* v___x_1672_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v_fvarId_1671_ = lean_ctor_get(v_a_1670_, 0);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1646_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1658_);
lean_inc(v_fvarId_1671_);
v___x_1672_ = lean_apply_9(v___y_1654_, v_fvarId_1671_, v___y_1649_, v___y_1658_, v___y_1648_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_, lean_box(0));
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_mk_empty_array_with_capacity(v___x_1674_);
v___x_1676_ = lean_array_push(v___x_1675_, v_a_1670_);
v___x_1677_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1678_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1653_, v___x_1676_, v_a_1673_, v___x_1677_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___f_1680_; lean_object* v___x_1681_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_n(v_a_1679_, 2);
lean_dec_ref_known(v___x_1678_, 1);
v___f_1680_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1680_, 0, v_a_1679_);
lean_closure_set(v___f_1680_, 1, v___x_1674_);
v___x_1681_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1653_, v_a_1660_, v___f_1680_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1693_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1693_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1679_);
lean_ctor_set(v___x_1686_, 1, v_a_1682_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1686_);
v___x_1688_ = v___x_1635_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1688_);
v___x_1690_ = v___x_1684_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1679_);
lean_del_object(v___x_1635_);
v_a_1694_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1681_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1681_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1660_);
lean_del_object(v___x_1635_);
v_a_1702_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1678_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1678_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_a_1670_);
lean_dec(v_a_1660_);
lean_del_object(v___x_1635_);
v_a_1710_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1672_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1672_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1649_);
lean_del_object(v___x_1635_);
v_a_1718_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1669_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1669_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_a_1666_);
v___x_1726_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1727_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1663_, v_a_1660_, v___x_1726_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1728_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_fvarId_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v_fvarId_1731_ = lean_ctor_get(v_a_1730_, 0);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1646_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1649_);
lean_inc(v_fvarId_1731_);
v___x_1732_ = lean_apply_9(v___y_1654_, v_fvarId_1731_, v___y_1649_, v___y_1658_, v___y_1648_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_, lean_box(0));
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_a_1730_);
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
v___x_1737_ = lean_array_push(v___x_1736_, v___x_1734_);
v___x_1738_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1737_, v_a_1733_, v___y_1649_, v___y_1658_, v___y_1648_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v___x_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1749_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_a_1739_);
v___x_1744_ = v___x_1635_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1744_);
v___x_1746_ = v___x_1741_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1635_);
v_a_1750_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1738_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1738_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1730_);
lean_dec_ref(v___y_1649_);
lean_del_object(v___x_1635_);
v_a_1758_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1732_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1732_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1649_);
lean_del_object(v___x_1635_);
v_a_1766_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1729_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1729_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1649_);
lean_del_object(v___x_1635_);
v_a_1774_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1727_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1727_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___x_1663_);
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1649_);
lean_del_object(v___x_1635_);
v_a_1782_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1665_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1665_);
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
lean_object* v___x_1790_; 
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_fType_1639_);
v___x_1790_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1653_, v_a_1660_, v___y_1657_, v___y_1646_, v___y_1655_, v___y_1647_, v___y_1650_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1801_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_a_1791_);
v___x_1796_ = v___x_1635_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_del_object(v___x_1635_);
v_a_1802_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1790_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1790_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_fType_1639_);
lean_del_object(v___x_1635_);
v_a_1810_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1661_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1661_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_fType_1639_);
lean_del_object(v___x_1635_);
v_a_1818_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1659_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1659_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
v___jp_1826_:
{
if (v___x_1644_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc_ref_n(v_args_1640_, 2);
lean_inc_ref(v_fType_1639_);
lean_inc_ref(v_value_1638_);
lean_inc_ref(v_params_1637_);
lean_dec(v_val_1633_);
v___x_1834_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1643_);
v___x_1835_ = l_Array_toSubarray___redArg(v_args_1640_, v___x_1834_, v___x_1643_);
lean_inc_ref(v___x_1835_);
v___x_1836_ = l_Subarray_copy___redArg(v___x_1835_);
v___x_1837_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1637_, v_value_1638_, v___x_1836_, v___x_1644_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v_params_1637_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v___f_1842_; uint8_t v___x_1843_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = 0;
v___x_1840_ = lean_box(v___x_1839_);
lean_inc_ref(v_k_1614_);
lean_inc(v_fvarId_1623_);
lean_inc(v___x_1643_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1841_, 0, v___x_1643_);
lean_closure_set(v___f_1841_, 1, v___x_1642_);
lean_closure_set(v___f_1841_, 2, v_fvarId_1623_);
lean_closure_set(v___f_1841_, 3, v_k_1614_);
lean_closure_set(v___f_1841_, 4, v_args_1640_);
lean_closure_set(v___f_1841_, 5, v___x_1840_);
lean_closure_set(v___f_1841_, 6, v___x_1834_);
lean_inc_ref(v___y_1829_);
lean_inc_ref(v___y_1827_);
lean_inc_ref(v___f_1841_);
lean_inc(v___y_1828_);
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1842_, 0, v___y_1828_);
lean_closure_set(v___f_1842_, 1, v___f_1841_);
lean_closure_set(v___f_1842_, 2, v___y_1827_);
lean_closure_set(v___f_1842_, 3, v___y_1829_);
v___x_1843_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1614_, v_fvarId_1623_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
if (v___x_1843_ == 0)
{
lean_dec(v___x_1643_);
v___y_1646_ = v___y_1830_;
v___y_1647_ = v___y_1832_;
v___y_1648_ = v___y_1829_;
v___y_1649_ = v___y_1827_;
v___y_1650_ = v___y_1833_;
v___y_1651_ = v_a_1838_;
v___y_1652_ = v___x_1835_;
v___y_1653_ = v___x_1839_;
v___y_1654_ = v___f_1841_;
v___y_1655_ = v___y_1831_;
v___y_1656_ = v___x_1834_;
v___y_1657_ = v___f_1842_;
v___y_1658_ = v___y_1828_;
goto v___jp_1645_;
}
else
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_nat_dec_eq(v___x_1642_, v___x_1643_);
lean_dec(v___x_1643_);
if (v___x_1844_ == 0)
{
v___y_1646_ = v___y_1830_;
v___y_1647_ = v___y_1832_;
v___y_1648_ = v___y_1829_;
v___y_1649_ = v___y_1827_;
v___y_1650_ = v___y_1833_;
v___y_1651_ = v_a_1838_;
v___y_1652_ = v___x_1835_;
v___y_1653_ = v___x_1839_;
v___y_1654_ = v___f_1841_;
v___y_1655_ = v___y_1831_;
v___y_1656_ = v___x_1834_;
v___y_1657_ = v___f_1842_;
v___y_1658_ = v___y_1828_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1845_; 
lean_dec_ref(v___f_1842_);
lean_dec_ref(v___f_1841_);
lean_dec_ref(v___x_1835_);
lean_dec_ref(v_fType_1639_);
lean_del_object(v___x_1635_);
v___x_1845_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1828_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1845_, 1);
lean_inc_ref(v___y_1832_);
v___x_1846_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1838_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v___y_1827_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1846_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1846_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_a_1838_);
lean_dec_ref(v___y_1827_);
v_a_1864_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1845_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1845_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___x_1835_);
lean_dec_ref(v___y_1827_);
lean_dec(v___x_1643_);
lean_dec_ref(v_args_1640_);
lean_dec_ref(v_fType_1639_);
lean_del_object(v___x_1635_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
v_a_1872_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1837_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1837_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v___x_1880_; 
lean_dec(v___x_1643_);
lean_del_object(v___x_1635_);
v___x_1880_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1633_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_fvarId_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_fvarId_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_fvarId_1882_);
v___x_1883_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1623_, v_fvarId_1882_, v___y_1828_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref_known(v___x_1883_, 1);
v___x_1884_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1828_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref_known(v___x_1884_, 1);
v___x_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1881_);
lean_ctor_set(v___x_1885_, 1, v_k_1614_);
lean_inc_ref(v___y_1832_);
v___x_1886_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1885_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v___y_1827_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1886_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1881_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_k_1614_);
v_a_1904_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1884_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1884_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1881_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_k_1614_);
v_a_1912_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1883_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1883_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___y_1827_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
v_a_1920_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1880_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1880_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec(v_a_1629_);
lean_del_object(v___x_1626_);
lean_dec(v_value_1624_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
v___x_1949_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1949_);
v___x_1951_ = v___x_1631_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_del_object(v___x_1626_);
lean_dec(v_value_1624_);
lean_dec(v_fvarId_1623_);
lean_dec_ref(v_k_1614_);
v_a_1954_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1628_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1628_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = 0;
v___x_1966_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_typeName_1979_; lean_object* v_discr_1980_; lean_object* v___x_1981_; lean_object* v_subst_1982_; uint8_t v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v_typeName_1979_ = lean_ctor_get(v_cases_1967_, 0);
v_discr_1980_ = lean_ctor_get(v_cases_1967_, 2);
v___x_1981_ = lean_st_ref_get(v_a_1969_);
v_subst_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_ref(v_subst_1982_);
lean_dec(v___x_1981_);
v___x_1983_ = 0;
v___x_1984_ = 0;
lean_inc(v_discr_1980_);
v___x_1985_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1982_, v_discr_1980_, v___x_1984_);
lean_dec_ref(v_subst_1982_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_fvarId_1986_; lean_object* v___x_1987_; 
v_fvarId_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_fvarId_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1986_, v_a_1970_, v_a_1972_, v_a_1974_);
lean_dec(v_fvarId_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2217_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2217_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2217_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
if (lean_obj_tag(v_a_1988_) == 1)
{
lean_object* v_val_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2212_; 
v_val_1992_ = lean_ctor_get(v_a_1988_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_a_1988_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_1994_ = v_a_1988_;
v_isShared_1995_ = v_isSharedCheck_2212_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_val_1992_);
lean_dec(v_a_1988_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2212_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v_env_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_st_ref_get(v_a_1974_);
v_env_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc_ref(v_env_1997_);
lean_dec(v___x_1996_);
v___x_1998_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1992_);
lean_inc(v___x_1998_);
v___x_1999_ = l_Lean_Environment_find_x3f(v_env_1997_, v___x_1998_, v___x_1984_);
if (lean_obj_tag(v___x_1999_) == 1)
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2211_; 
v_val_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2211_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2211_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_val_2000_) == 6)
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2210_; 
v_val_2004_ = lean_ctor_get(v_val_2000_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_val_2000_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2006_ = v_val_2000_;
v_isShared_2007_ = v_isSharedCheck_2210_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v_val_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2210_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_induct_2008_; uint8_t v___x_2009_; 
v_induct_2008_ = lean_ctor_get(v_val_2004_, 1);
lean_inc(v_induct_2008_);
lean_dec_ref(v_val_2004_);
v___x_2009_ = lean_name_eq(v_typeName_1979_, v_induct_2008_);
lean_dec(v_induct_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_del_object(v___x_2006_);
lean_del_object(v___x_2002_);
lean_dec(v___x_1998_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
lean_dec_ref(v_cases_1967_);
v___x_2010_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2010_);
v___x_2012_ = v___x_1990_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
lean_object* v___x_2014_; lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2209_; 
lean_del_object(v___x_1990_);
v___x_2014_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1983_, v_cases_1967_, v___x_1998_);
v_fst_2015_ = lean_ctor_get(v___x_2014_, 0);
v_snd_2016_ = lean_ctor_get(v___x_2014_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2018_ = v___x_2014_;
v_isShared_2019_ = v_isSharedCheck_2209_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2209_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 4);
lean_ctor_set(v___x_2006_, 0, v_snd_2016_);
v___x_2021_ = v___x_2006_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_snd_2016_);
v___x_2021_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1983_, v___x_2021_, v_a_1972_);
lean_dec_ref(v___x_2021_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref_known(v___x_2022_, 1);
v___x_2023_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1969_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_dec_ref_known(v___x_2023_, 1);
if (lean_obj_tag(v_fst_2015_) == 0)
{
if (lean_obj_tag(v_val_1992_) == 0)
{
lean_object* v_params_2024_; lean_object* v_code_2025_; lean_object* v_val_2026_; lean_object* v_args_2027_; lean_object* v_lower_2029_; lean_object* v_upper_2030_; lean_object* v_numParams_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_1994_);
v_params_2024_ = lean_ctor_get(v_fst_2015_, 1);
lean_inc_ref(v_params_2024_);
v_code_2025_ = lean_ctor_get(v_fst_2015_, 2);
lean_inc_ref(v_code_2025_);
lean_dec_ref_known(v_fst_2015_, 3);
v_val_2026_ = lean_ctor_get(v_val_1992_, 0);
lean_inc_ref(v_val_2026_);
v_args_2027_ = lean_ctor_get(v_val_1992_, 1);
lean_inc_ref(v_args_2027_);
lean_dec_ref_known(v_val_1992_, 2);
v_numParams_2073_ = lean_ctor_get(v_val_2026_, 3);
lean_inc(v_numParams_2073_);
lean_dec_ref(v_val_2026_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_array_get_size(v_args_2027_);
v___x_2076_ = lean_nat_dec_le(v_numParams_2073_, v___x_2074_);
if (v___x_2076_ == 0)
{
v_lower_2029_ = v_numParams_2073_;
v_upper_2030_ = v___x_2075_;
goto v___jp_2028_;
}
else
{
lean_dec(v_numParams_2073_);
v_lower_2029_ = v___x_2074_;
v_upper_2030_ = v___x_2075_;
goto v___jp_2028_;
}
v___jp_2028_:
{
lean_object* v___x_2031_; size_t v_sz_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = l_Array_toSubarray___redArg(v_args_2027_, v_lower_2029_, v_upper_2030_);
v_sz_2032_ = lean_array_size(v_params_2024_);
v___x_2033_ = ((size_t)0ULL);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2024_, v_sz_2032_, v___x_2033_, v___x_2031_, v_a_1969_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2034_, 1);
lean_inc_ref(v_a_1973_);
v___x_2035_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2025_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1983_, v_params_2024_, v_a_1972_);
lean_dec_ref(v_params_2024_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2037_, 0);
lean_dec(v_unused_2048_);
v___x_2039_ = v___x_2037_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v___x_2037_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_2036_);
v___x_2042_ = v___x_2002_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2036_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_2036_);
lean_del_object(v___x_2002_);
v_a_2049_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2037_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2037_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_params_2024_);
lean_del_object(v___x_2002_);
v_a_2057_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2035_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2035_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_code_2025_);
lean_dec_ref(v_params_2024_);
lean_del_object(v___x_2002_);
v_a_2065_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2034_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2034_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v_params_2077_; lean_object* v_code_2078_; lean_object* v_n_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2170_; 
v_params_2077_ = lean_ctor_get(v_fst_2015_, 1);
lean_inc_ref(v_params_2077_);
v_code_2078_ = lean_ctor_get(v_fst_2015_, 2);
lean_inc_ref(v_code_2078_);
lean_dec_ref_known(v_fst_2015_, 3);
v_n_2079_ = lean_ctor_get(v_val_1992_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_val_1992_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2081_ = v_val_1992_;
v_isShared_2082_ = v_isSharedCheck_2170_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_n_2079_);
lean_dec(v_val_1992_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2170_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_zero_2083_; uint8_t v_isZero_2084_; 
v_zero_2083_ = lean_unsigned_to_nat(0u);
v_isZero_2084_ = lean_nat_dec_eq(v_n_2079_, v_zero_2083_);
if (v_isZero_2084_ == 1)
{
lean_object* v___x_2085_; 
lean_del_object(v___x_2081_);
lean_dec(v_n_2079_);
lean_dec_ref(v_params_2077_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_1994_);
lean_inc_ref(v_a_1973_);
v___x_2085_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2078_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2096_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_2086_);
v___x_2091_ = v___x_2002_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2091_);
v___x_2093_ = v___x_2088_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_2002_);
v_a_2097_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2085_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2085_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_one_2105_; lean_object* v_n_2106_; lean_object* v___x_2108_; 
v_one_2105_ = lean_unsigned_to_nat(1u);
v_n_2106_ = lean_nat_sub(v_n_2079_, v_one_2105_);
lean_dec(v_n_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 0);
lean_ctor_set(v___x_2081_, 0, v_n_2106_);
v___x_2108_ = v___x_2081_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_n_2106_);
v___x_2108_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 0);
lean_ctor_set(v___x_1994_, 0, v___x_2108_);
v___x_2110_ = v___x_1994_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2112_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1983_, v___x_2110_, v___x_2111_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_fvarId_2116_; lean_object* v_fvarId_2117_; lean_object* v___x_2118_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2115_ = lean_array_get_borrowed(v___x_2114_, v_params_2077_, v_zero_2083_);
v_fvarId_2116_ = lean_ctor_get(v___x_2115_, 0);
v_fvarId_2117_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_fvarId_2117_);
lean_inc(v_fvarId_2116_);
v___x_2118_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2116_, v_fvarId_2117_, v_a_1969_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref_known(v___x_2118_, 1);
lean_inc_ref(v_a_1973_);
v___x_2119_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2078_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1983_, v_params_2077_, v_a_1972_);
lean_dec_ref(v_params_2077_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2134_; 
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v___x_2121_, 0);
lean_dec(v_unused_2135_);
v___x_2123_ = v___x_2121_;
v_isShared_2124_ = v_isSharedCheck_2134_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2121_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2134_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v_a_2120_);
lean_ctor_set(v___x_2018_, 0, v_a_2113_);
v___x_2126_ = v___x_2018_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2113_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_a_2120_);
v___x_2126_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2126_);
v___x_2128_ = v___x_2002_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2128_);
v___x_2130_ = v___x_2123_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2120_);
lean_dec(v_a_2113_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2136_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2121_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2121_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_params_2077_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2144_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2119_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2119_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_code_2078_);
lean_dec_ref(v_params_2077_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2152_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2118_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2118_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_code_2078_);
lean_dec_ref(v_params_2077_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2160_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2112_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2112_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
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
lean_object* v_code_2171_; lean_object* v___x_2172_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
v_code_2171_ = lean_ctor_get(v_fst_2015_, 0);
lean_inc_ref(v_code_2171_);
lean_dec_ref_known(v_fst_2015_, 1);
lean_inc_ref(v_a_1973_);
v___x_2172_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2171_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2183_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_2173_);
v___x_2178_ = v___x_2002_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_del_object(v___x_2002_);
v_a_2184_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2172_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2172_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2018_);
lean_dec(v_fst_2015_);
lean_del_object(v___x_2002_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
v_a_2192_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2023_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2023_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_2018_);
lean_dec(v_fst_2015_);
lean_del_object(v___x_2002_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
v_a_2200_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2022_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2022_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
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
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
lean_dec(v___x_1998_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
lean_del_object(v___x_1990_);
lean_dec_ref(v_cases_1967_);
goto v___jp_1976_;
}
}
}
else
{
lean_dec(v___x_1999_);
lean_dec(v___x_1998_);
lean_del_object(v___x_1994_);
lean_dec(v_val_1992_);
lean_del_object(v___x_1990_);
lean_dec_ref(v_cases_1967_);
goto v___jp_1976_;
}
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec(v_a_1988_);
lean_dec_ref(v_cases_1967_);
v___x_2213_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2213_);
v___x_2215_ = v___x_1990_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_cases_1967_);
v_a_2218_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_1987_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_1987_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v___x_2226_; 
lean_dec_ref(v_cases_1967_);
v___x_2226_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1983_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_a_2236_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2226_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2226_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
v___jp_1976_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2244_, lean_object* v_i_2245_, lean_object* v_as_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_array_get_size(v_as_2246_);
v___x_2256_ = lean_nat_dec_lt(v_i_2245_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_as_2246_);
return v___x_2257_;
}
else
{
lean_object* v_a_2258_; lean_object* v_a_2260_; 
v_a_2258_ = lean_array_fget_borrowed(v_as_2246_, v_i_2245_);
if (lean_obj_tag(v_a_2258_) == 0)
{
lean_object* v_ctorName_2271_; lean_object* v_params_2272_; lean_object* v_code_2273_; uint8_t v___x_2296_; uint8_t v_a_2298_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_ctorName_2271_ = lean_ctor_get(v_a_2258_, 0);
v_params_2272_ = lean_ctor_get(v_a_2258_, 1);
v_code_2273_ = lean_ctor_get(v_a_2258_, 2);
v___x_2296_ = 0;
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_get_size(v_params_2272_);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
v_a_2298_ = v___x_2331_;
goto v___jp_2297_;
}
else
{
if (v___x_2331_ == 0)
{
v_a_2298_ = v___x_2331_;
goto v___jp_2297_;
}
else
{
size_t v___x_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = ((size_t)0ULL);
v___x_2333_ = lean_usize_of_nat(v___x_2330_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2272_, v___x_2332_, v___x_2333_, v___y_2253_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
v_a_2298_ = v___x_2336_;
goto v___jp_2297_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2337_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2334_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2334_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
v___jp_2274_:
{
lean_object* v___x_2275_; 
lean_inc_ref(v_params_2272_);
lean_inc(v_ctorName_2271_);
lean_inc(v_fvarId_2244_);
v___x_2275_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2244_, v_ctorName_2271_, v_params_2272_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v_code_2273_);
v___x_2277_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2273_, v___y_2247_, v___y_2248_, v_a_2276_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v_a_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
lean_inc_ref(v_a_2258_);
v___x_2279_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2258_, v_a_2278_);
v_a_2260_ = v___x_2279_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2280_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2277_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2277_);
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
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2288_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2275_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2275_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
v___jp_2297_:
{
if (lean_obj_tag(v_code_2273_) == 6)
{
goto v___jp_2274_;
}
else
{
if (v_a_2298_ == 0)
{
goto v___jp_2274_;
}
else
{
lean_object* v___x_2299_; 
lean_inc_ref(v_code_2273_);
v___x_2299_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2296_, v_code_2273_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2296_, v_code_2273_, v___y_2251_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2302_; 
lean_dec_ref_known(v___x_2301_, 1);
v___x_2302_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2248_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_a_2300_);
lean_inc_ref(v_a_2258_);
v___x_2304_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2258_, v___x_2303_);
v_a_2260_ = v___x_2304_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2300_);
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2305_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2302_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2302_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2300_);
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2313_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2301_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2301_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2321_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2299_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2299_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2345_; lean_object* v___x_2346_; 
v_code_2345_ = lean_ctor_get(v_a_2258_, 0);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v_code_2345_);
v___x_2346_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2345_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
lean_inc_ref(v_a_2258_);
v___x_2348_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2258_, v_a_2347_);
v_a_2260_ = v___x_2348_;
goto v___jp_2259_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v_as_2246_);
lean_dec(v_i_2245_);
lean_dec(v_fvarId_2244_);
v_a_2349_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2346_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2346_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
v___jp_2259_:
{
size_t v___x_2261_; size_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = lean_ptr_addr(v_a_2258_);
v___x_2262_ = lean_ptr_addr(v_a_2260_);
v___x_2263_ = lean_usize_dec_eq(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_add(v_i_2245_, v___x_2264_);
v___x_2266_ = lean_array_fset(v_as_2246_, v_i_2245_, v_a_2260_);
lean_dec(v_i_2245_);
v_i_2245_ = v___x_2265_;
v_as_2246_ = v___x_2266_;
goto _start;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v_a_2260_);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_nat_add(v_i_2245_, v___x_2268_);
lean_dec(v_i_2245_);
v_i_2245_ = v___x_2269_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___y_2368_; lean_object* v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2377_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2404_; uint8_t v___y_2405_; lean_object* v_decl_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2455_; uint8_t v___y_2456_; lean_object* v_decl_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_decl_2476_; lean_object* v_k_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v_decl_2748_; lean_object* v_fvarId_2749_; lean_object* v_type_2750_; lean_object* v_value_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2792_; lean_object* v___y_2793_; uint8_t v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___y_2842_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; uint8_t v___y_2935_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v_fileName_3244_; lean_object* v_fileMap_3245_; lean_object* v_options_3246_; lean_object* v_currRecDepth_3247_; lean_object* v_maxRecDepth_3248_; lean_object* v_ref_3249_; lean_object* v_currNamespace_3250_; lean_object* v_openDecls_3251_; lean_object* v_initHeartbeats_3252_; lean_object* v_maxHeartbeats_3253_; lean_object* v_quotContext_3254_; lean_object* v_currMacroScope_3255_; uint8_t v_diag_3256_; lean_object* v_cancelTk_x3f_3257_; uint8_t v_suppressElabErrors_3258_; lean_object* v_inheritedTraceOptions_3259_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v_fileName_3244_ = lean_ctor_get(v_a_2364_, 0);
v_fileMap_3245_ = lean_ctor_get(v_a_2364_, 1);
v_options_3246_ = lean_ctor_get(v_a_2364_, 2);
v_currRecDepth_3247_ = lean_ctor_get(v_a_2364_, 3);
v_maxRecDepth_3248_ = lean_ctor_get(v_a_2364_, 4);
v_ref_3249_ = lean_ctor_get(v_a_2364_, 5);
v_currNamespace_3250_ = lean_ctor_get(v_a_2364_, 6);
v_openDecls_3251_ = lean_ctor_get(v_a_2364_, 7);
v_initHeartbeats_3252_ = lean_ctor_get(v_a_2364_, 8);
v_maxHeartbeats_3253_ = lean_ctor_get(v_a_2364_, 9);
v_quotContext_3254_ = lean_ctor_get(v_a_2364_, 10);
v_currMacroScope_3255_ = lean_ctor_get(v_a_2364_, 11);
v_diag_3256_ = lean_ctor_get_uint8(v_a_2364_, sizeof(void*)*14);
v_cancelTk_x3f_3257_ = lean_ctor_get(v_a_2364_, 12);
v_suppressElabErrors_3258_ = lean_ctor_get_uint8(v_a_2364_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3259_ = lean_ctor_get(v_a_2364_, 13);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_nat_dec_eq(v_maxRecDepth_3248_, v___x_3289_);
if (v___x_3290_ == 0)
{
uint8_t v___x_3291_; 
v___x_3291_ = lean_nat_dec_eq(v_currRecDepth_3247_, v_maxRecDepth_3248_);
if (v___x_3291_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3259_);
lean_inc(v_cancelTk_x3f_3257_);
lean_inc(v_currMacroScope_3255_);
lean_inc(v_quotContext_3254_);
lean_inc(v_maxHeartbeats_3253_);
lean_inc(v_initHeartbeats_3252_);
lean_inc(v_openDecls_3251_);
lean_inc(v_currNamespace_3250_);
lean_inc(v_ref_3249_);
lean_inc(v_maxRecDepth_3248_);
lean_inc(v_currRecDepth_3247_);
lean_inc_ref(v_options_3246_);
lean_inc_ref(v_fileMap_3245_);
lean_inc_ref(v_fileName_3244_);
lean_dec_ref(v_a_2364_);
goto v___jp_3260_;
}
else
{
lean_object* v___x_3292_; 
lean_dec_ref(v_code_2358_);
v___x_3292_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec_ref(v_a_2364_);
return v___x_3292_;
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3259_);
lean_inc(v_cancelTk_x3f_3257_);
lean_inc(v_currMacroScope_3255_);
lean_inc(v_quotContext_3254_);
lean_inc(v_maxHeartbeats_3253_);
lean_inc(v_initHeartbeats_3252_);
lean_inc(v_openDecls_3251_);
lean_inc(v_currNamespace_3250_);
lean_inc(v_ref_3249_);
lean_inc(v_maxRecDepth_3248_);
lean_inc(v_currRecDepth_3247_);
lean_inc_ref(v_options_3246_);
lean_inc_ref(v_fileMap_3245_);
lean_inc_ref(v_fileName_3244_);
lean_dec_ref(v_a_2364_);
goto v___jp_3260_;
}
v___jp_2367_:
{
if (v___y_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v_code_2358_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___y_2368_);
lean_ctor_set(v___x_2371_, 1, v___y_2369_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; 
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___y_2368_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_code_2358_);
return v___x_2373_;
}
}
v___jp_2374_:
{
if (v___y_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_code_2358_);
v___x_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___y_2375_);
lean_ctor_set(v___x_2378_, 1, v___y_2376_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; 
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2375_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_code_2358_);
return v___x_2380_;
}
}
v___jp_2381_:
{
switch(lean_obj_tag(v_code_2358_))
{
case 1:
{
lean_object* v_decl_2384_; lean_object* v_k_2385_; size_t v___x_2386_; size_t v___x_2387_; uint8_t v___x_2388_; 
v_decl_2384_ = lean_ctor_get(v_code_2358_, 0);
v_k_2385_ = lean_ctor_get(v_code_2358_, 1);
v___x_2386_ = lean_ptr_addr(v_k_2385_);
v___x_2387_ = lean_ptr_addr(v___y_2383_);
v___x_2388_ = lean_usize_dec_eq(v___x_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
v___y_2368_ = v___y_2382_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___x_2388_;
goto v___jp_2367_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; uint8_t v___x_2391_; 
v___x_2389_ = lean_ptr_addr(v_decl_2384_);
v___x_2390_ = lean_ptr_addr(v___y_2382_);
v___x_2391_ = lean_usize_dec_eq(v___x_2389_, v___x_2390_);
v___y_2368_ = v___y_2382_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___x_2391_;
goto v___jp_2367_;
}
}
case 2:
{
lean_object* v_decl_2392_; lean_object* v_k_2393_; size_t v___x_2394_; size_t v___x_2395_; uint8_t v___x_2396_; 
v_decl_2392_ = lean_ctor_get(v_code_2358_, 0);
v_k_2393_ = lean_ctor_get(v_code_2358_, 1);
v___x_2394_ = lean_ptr_addr(v_k_2393_);
v___x_2395_ = lean_ptr_addr(v___y_2383_);
v___x_2396_ = lean_usize_dec_eq(v___x_2394_, v___x_2395_);
if (v___x_2396_ == 0)
{
v___y_2375_ = v___y_2382_;
v___y_2376_ = v___y_2383_;
v___y_2377_ = v___x_2396_;
goto v___jp_2374_;
}
else
{
size_t v___x_2397_; size_t v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = lean_ptr_addr(v_decl_2392_);
v___x_2398_ = lean_ptr_addr(v___y_2382_);
v___x_2399_ = lean_usize_dec_eq(v___x_2397_, v___x_2398_);
v___y_2375_ = v___y_2382_;
v___y_2376_ = v___y_2383_;
v___y_2377_ = v___x_2399_;
goto v___jp_2374_;
}
}
default: 
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_code_2358_);
v___x_2400_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2401_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
}
v___jp_2403_:
{
lean_object* v___x_2414_; 
lean_inc_ref(v___y_2412_);
v___x_2414_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2404_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v_fvarId_2416_; lean_object* v___x_2417_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v_fvarId_2416_ = lean_ctor_get(v_decl_2406_, 0);
v___x_2417_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2416_, v___y_2408_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; uint8_t v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = lean_unbox(v_a_2418_);
lean_dec(v_a_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_code_2358_);
v___x_2420_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2406_, v___y_2408_, v___y_2411_);
lean_dec_ref(v_decl_2406_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v___x_2420_, 0);
lean_dec(v_unused_2428_);
v___x_2422_ = v___x_2420_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_dec(v___x_2420_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_a_2415_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2415_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_a_2415_);
v_a_2429_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2420_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
if (v___y_2405_ == 0)
{
lean_dec_ref(v___y_2412_);
v___y_2382_ = v_decl_2406_;
v___y_2383_ = v_a_2415_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2437_; 
lean_inc_ref(v_decl_2406_);
v___x_2437_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec_ref(v___y_2412_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_dec_ref_known(v___x_2437_, 1);
v___y_2382_ = v_decl_2406_;
v___y_2383_ = v_a_2415_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_a_2415_);
lean_dec_ref(v_decl_2406_);
lean_dec_ref(v_code_2358_);
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2415_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_decl_2406_);
lean_dec_ref(v_code_2358_);
v_a_2446_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2417_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2417_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_decl_2406_);
lean_dec_ref(v_code_2358_);
return v___x_2414_;
}
}
v___jp_2454_:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___y_2404_ = v___y_2455_;
v___y_2405_ = v___y_2456_;
v_decl_2406_ = v_a_2466_;
v___y_2407_ = v___y_2458_;
v___y_2408_ = v___y_2459_;
v___y_2409_ = v___y_2460_;
v___y_2410_ = v___y_2461_;
v___y_2411_ = v___y_2462_;
v___y_2412_ = v___y_2463_;
v___y_2413_ = v___y_2464_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v___y_2463_);
lean_dec_ref(v___y_2455_);
lean_dec_ref(v_code_2358_);
v_a_2467_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2465_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2465_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
v___jp_2475_:
{
lean_object* v_fvarId_2485_; lean_object* v_params_2486_; lean_object* v_type_2487_; lean_object* v___x_2488_; 
v_fvarId_2485_ = lean_ctor_get(v_decl_2476_, 0);
v_params_2486_ = lean_ctor_get(v_decl_2476_, 2);
v_type_2487_ = lean_ctor_get(v_decl_2476_, 3);
v___x_2488_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2485_, v___y_2479_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; uint8_t v___x_2490_; uint8_t v___x_2491_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = 0;
v___x_2491_ = lean_unbox(v_a_2489_);
if (v___x_2491_ == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2358_);
if (v___x_2492_ == 0)
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_unbox(v_a_2489_);
lean_dec(v_a_2489_);
v___y_2455_ = v_k_2477_;
v___y_2456_ = v___x_2493_;
v_decl_2457_ = v_decl_2476_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2484_;
goto v___jp_2454_;
}
else
{
uint8_t v___x_2494_; 
lean_inc_ref(v_type_2487_);
v___x_2494_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2487_, v_params_2486_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_unbox(v_a_2489_);
lean_dec(v_a_2489_);
v___y_2455_ = v_k_2477_;
v___y_2456_ = v___x_2495_;
v_decl_2457_ = v_decl_2476_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2484_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2496_; lean_object* v_subst_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_st_ref_get(v___y_2479_);
v_subst_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc_ref(v_subst_2497_);
lean_dec(v___x_2496_);
v___x_2498_ = lean_unbox(v_a_2489_);
v___x_2499_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2490_, v___x_2498_, v_decl_2476_, v_subst_2497_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec_ref(v_subst_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2500_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2479_);
if (lean_obj_tag(v___x_2503_) == 0)
{
uint8_t v___x_2504_; 
lean_dec_ref_known(v___x_2503_, 1);
v___x_2504_ = lean_unbox(v_a_2489_);
lean_dec(v_a_2489_);
v___y_2455_ = v_k_2477_;
v___y_2456_ = v___x_2504_;
v_decl_2457_ = v_a_2502_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2484_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2502_);
lean_dec(v_a_2489_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_k_2477_);
lean_dec_ref(v_code_2358_);
v_a_2505_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2503_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2503_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_a_2489_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_k_2477_);
lean_dec_ref(v_code_2358_);
v_a_2513_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2501_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2501_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_a_2489_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_k_2477_);
lean_dec_ref(v_code_2358_);
v_a_2521_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2499_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2499_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v_subst_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2529_ = lean_st_ref_get(v___y_2479_);
v_subst_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_ref(v_subst_2530_);
lean_dec(v___x_2529_);
v___x_2531_ = 0;
v___x_2532_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2490_, v___x_2531_, v_decl_2476_, v_subst_2530_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec_ref(v_subst_2530_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = lean_unbox(v_a_2489_);
lean_dec(v_a_2489_);
v___y_2404_ = v_k_2477_;
v___y_2405_ = v___x_2534_;
v_decl_2406_ = v_a_2533_;
v___y_2407_ = v___y_2478_;
v___y_2408_ = v___y_2479_;
v___y_2409_ = v___y_2480_;
v___y_2410_ = v___y_2481_;
v___y_2411_ = v___y_2482_;
v___y_2412_ = v___y_2483_;
v___y_2413_ = v___y_2484_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2489_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_k_2477_);
lean_dec_ref(v_code_2358_);
v_a_2535_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2532_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2532_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_k_2477_);
lean_dec_ref(v_decl_2476_);
lean_dec_ref(v_code_2358_);
v_a_2543_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2488_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2488_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
v___jp_2551_:
{
if (v___y_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec_ref(v_code_2358_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2553_);
lean_ctor_set(v___x_2555_, 1, v___y_2552_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; 
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2552_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_code_2358_);
return v___x_2557_;
}
}
v___jp_2558_:
{
lean_object* v___x_2569_; 
lean_inc_ref(v___y_2565_);
v___x_2569_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2565_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
if (lean_obj_tag(v_a_2570_) == 1)
{
lean_object* v_val_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_val_2571_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_val_2571_);
lean_dec_ref_known(v_a_2570_, 1);
v___x_2572_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2567_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref_known(v___x_2572_, 1);
lean_inc_ref(v___y_2564_);
v___x_2573_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2568_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2571_, v_a_2574_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
lean_dec_ref(v___y_2564_);
lean_dec(v_val_2571_);
return v___x_2575_;
}
else
{
lean_dec(v_val_2571_);
lean_dec_ref(v___y_2564_);
return v___x_2573_;
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_val_2571_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2564_);
v_a_2576_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2572_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2572_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v___x_2584_; 
lean_dec(v_a_2570_);
lean_inc_ref(v___y_2565_);
v___x_2584_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2565_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
if (lean_obj_tag(v_a_2585_) == 1)
{
lean_object* v_val_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_val_2586_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v_a_2585_, 1);
v___x_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_val_2586_);
lean_ctor_set(v___x_2587_, 1, v___y_2568_);
v_code_2358_ = v___x_2587_;
v_a_2359_ = v___y_2562_;
v_a_2360_ = v___y_2567_;
v_a_2361_ = v___y_2563_;
v_a_2362_ = v___y_2559_;
v_a_2363_ = v___y_2566_;
v_a_2364_ = v___y_2564_;
v_a_2365_ = v___y_2560_;
goto _start;
}
else
{
lean_object* v_fvarId_2589_; lean_object* v_value_2590_; lean_object* v___x_2591_; 
lean_dec(v_a_2585_);
v_fvarId_2589_ = lean_ctor_get(v___y_2565_, 0);
v_value_2590_ = lean_ctor_get(v___y_2565_, 3);
v___x_2591_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_val_2593_; lean_object* v___x_2594_; 
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_val_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v_a_2592_, 1);
lean_inc(v_fvarId_2589_);
v___x_2594_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2589_, v_val_2593_, v___y_2567_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; 
lean_dec_ref_known(v___x_2594_, 1);
v___x_2595_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2565_, v___y_2567_, v___y_2566_);
lean_dec_ref(v___y_2565_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
v_code_2358_ = v___y_2568_;
v_a_2359_ = v___y_2562_;
v_a_2360_ = v___y_2567_;
v_a_2361_ = v___y_2563_;
v_a_2362_ = v___y_2559_;
v_a_2363_ = v___y_2566_;
v_a_2364_ = v___y_2564_;
v_a_2365_ = v___y_2560_;
goto _start;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2564_);
v_a_2597_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
v_a_2605_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2594_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2594_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2592_);
lean_inc_ref(v___y_2568_);
lean_inc_ref(v___y_2565_);
v___x_2613_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2565_, v___y_2568_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
if (lean_obj_tag(v_a_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_val_2615_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v_a_2614_, 1);
v___x_2616_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2565_, v___y_2567_, v___y_2566_);
lean_dec_ref(v___y_2565_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v___x_2616_, 0);
lean_dec(v_unused_2624_);
v___x_2618_ = v___x_2616_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_dec(v___x_2616_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_val_2615_);
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_val_2615_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_val_2615_);
v_a_2625_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2616_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2616_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_a_2614_);
lean_inc(v_value_2590_);
v___x_2633_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2590_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
if (lean_obj_tag(v_a_2634_) == 1)
{
lean_object* v_val_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2638_; 
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_val_2635_ = lean_ctor_get(v_a_2634_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v_a_2634_, 1);
v_fst_2636_ = lean_ctor_get(v_val_2635_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v_val_2635_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_val_2635_);
lean_inc(v_fvarId_2589_);
v___x_2638_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2589_, v_snd_2637_, v___y_2567_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2639_; 
lean_dec_ref_known(v___x_2638_, 1);
v___x_2639_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2565_, v___y_2567_, v___y_2566_);
lean_dec_ref(v___y_2565_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref_known(v___x_2639_, 1);
lean_inc_ref(v___y_2564_);
v___x_2640_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2568_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2636_, v_a_2641_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
lean_dec_ref(v___y_2564_);
lean_dec(v_fst_2636_);
return v___x_2642_;
}
else
{
lean_dec(v_fst_2636_);
lean_dec_ref(v___y_2564_);
return v___x_2640_;
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_fst_2636_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2564_);
v_a_2643_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2639_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_fst_2636_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
v_a_2651_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2638_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2638_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v___x_2659_; 
lean_dec(v_a_2634_);
lean_inc_ref(v___y_2564_);
lean_inc_ref(v___y_2568_);
v___x_2659_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2568_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2589_, v___y_2567_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = lean_unbox(v_a_2662_);
lean_dec(v_a_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v___x_2664_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2565_, v___y_2567_, v___y_2566_);
lean_dec_ref(v___y_2565_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2664_, 0);
lean_dec(v_unused_2672_);
v___x_2666_ = v___x_2664_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v___x_2664_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v_a_2660_);
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2660_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_a_2660_);
v_a_2673_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2664_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2664_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v___x_2681_; 
lean_inc_ref(v___y_2565_);
v___x_2681_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2565_, v___y_2562_, v___y_2567_, v___y_2563_, v___y_2559_, v___y_2566_, v___y_2564_, v___y_2560_);
lean_dec_ref(v___y_2564_);
if (lean_obj_tag(v___x_2681_) == 0)
{
size_t v___x_2682_; size_t v___x_2683_; uint8_t v___x_2684_; 
lean_dec_ref_known(v___x_2681_, 1);
v___x_2682_ = lean_ptr_addr(v___y_2568_);
lean_dec_ref(v___y_2568_);
v___x_2683_ = lean_ptr_addr(v_a_2660_);
v___x_2684_ = lean_usize_dec_eq(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_dec_ref(v___y_2561_);
v___y_2552_ = v_a_2660_;
v___y_2553_ = v___y_2565_;
v___y_2554_ = v___x_2684_;
goto v___jp_2551_;
}
else
{
size_t v___x_2685_; size_t v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_ptr_addr(v___y_2561_);
lean_dec_ref(v___y_2561_);
v___x_2686_ = lean_ptr_addr(v___y_2565_);
v___x_2687_ = lean_usize_dec_eq(v___x_2685_, v___x_2686_);
v___y_2552_ = v_a_2660_;
v___y_2553_ = v___y_2565_;
v___y_2554_ = v___x_2687_;
goto v___jp_2551_;
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2660_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2688_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2681_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2681_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2660_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2696_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2661_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2661_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2704_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2633_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2633_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2712_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2613_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2613_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2720_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2591_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2591_);
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
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2728_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2584_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2584_);
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
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v_code_2358_);
v_a_2736_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2569_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2569_);
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
v___jp_2744_:
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Lean_Expr_isErased(v_type_2750_);
lean_dec_ref(v_type_2750_);
if (v___x_2759_ == 0)
{
lean_dec(v_value_2751_);
lean_dec(v_fvarId_2749_);
v___y_2559_ = v___y_2755_;
v___y_2560_ = v___y_2758_;
v___y_2561_ = v___y_2745_;
v___y_2562_ = v___y_2752_;
v___y_2563_ = v___y_2754_;
v___y_2564_ = v___y_2757_;
v___y_2565_ = v_decl_2748_;
v___y_2566_ = v___y_2756_;
v___y_2567_ = v___y_2753_;
v___y_2568_ = v___y_2747_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = lean_box(1);
v___x_2761_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2746_, v_value_2751_, v___x_2760_);
lean_dec(v_value_2751_);
if (v___x_2761_ == 0)
{
if (v___x_2759_ == 0)
{
lean_dec(v_fvarId_2749_);
v___y_2559_ = v___y_2755_;
v___y_2560_ = v___y_2758_;
v___y_2561_ = v___y_2745_;
v___y_2562_ = v___y_2752_;
v___y_2563_ = v___y_2754_;
v___y_2564_ = v___y_2757_;
v___y_2565_ = v_decl_2748_;
v___y_2566_ = v___y_2756_;
v___y_2567_ = v___y_2753_;
v___y_2568_ = v___y_2747_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2762_; lean_object* v_subst_2763_; lean_object* v_used_2764_; lean_object* v_binderRenaming_2765_; lean_object* v_funDeclInfoMap_2766_; uint8_t v_simplified_2767_; lean_object* v_visited_2768_; lean_object* v_inline_2769_; lean_object* v_inlineLocal_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v___y_2745_);
lean_dec_ref(v_code_2358_);
v___x_2762_ = lean_st_ref_take(v___y_2753_);
v_subst_2763_ = lean_ctor_get(v___x_2762_, 0);
v_used_2764_ = lean_ctor_get(v___x_2762_, 1);
v_binderRenaming_2765_ = lean_ctor_get(v___x_2762_, 2);
v_funDeclInfoMap_2766_ = lean_ctor_get(v___x_2762_, 3);
v_simplified_2767_ = lean_ctor_get_uint8(v___x_2762_, sizeof(void*)*7);
v_visited_2768_ = lean_ctor_get(v___x_2762_, 4);
v_inline_2769_ = lean_ctor_get(v___x_2762_, 5);
v_inlineLocal_2770_ = lean_ctor_get(v___x_2762_, 6);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2772_ = v___x_2762_;
v_isShared_2773_ = v_isSharedCheck_2790_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_inlineLocal_2770_);
lean_inc(v_inline_2769_);
lean_inc(v_visited_2768_);
lean_inc(v_funDeclInfoMap_2766_);
lean_inc(v_binderRenaming_2765_);
lean_inc(v_used_2764_);
lean_inc(v_subst_2763_);
lean_dec(v___x_2762_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2790_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2774_ = lean_box(0);
v___x_2775_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2763_, v_fvarId_2749_, v___x_2774_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2775_);
v___x_2777_ = v___x_2772_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_used_2764_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_binderRenaming_2765_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_funDeclInfoMap_2766_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_visited_2768_);
lean_ctor_set(v_reuseFailAlloc_2789_, 5, v_inline_2769_);
lean_ctor_set(v_reuseFailAlloc_2789_, 6, v_inlineLocal_2770_);
lean_ctor_set_uint8(v_reuseFailAlloc_2789_, sizeof(void*)*7, v_simplified_2767_);
v___x_2777_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_st_ref_set(v___y_2753_, v___x_2777_);
v___x_2779_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2748_, v___y_2753_, v___y_2756_);
lean_dec_ref(v_decl_2748_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_dec_ref_known(v___x_2779_, 1);
v_code_2358_ = v___y_2747_;
v_a_2359_ = v___y_2752_;
v_a_2360_ = v___y_2753_;
v_a_2361_ = v___y_2754_;
v_a_2362_ = v___y_2755_;
v_a_2363_ = v___y_2756_;
v_a_2364_ = v___y_2757_;
v_a_2365_ = v___y_2758_;
goto _start;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v___y_2757_);
lean_dec_ref(v___y_2747_);
v_a_2781_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2749_);
v___y_2559_ = v___y_2755_;
v___y_2560_ = v___y_2758_;
v___y_2561_ = v___y_2745_;
v___y_2562_ = v___y_2752_;
v___y_2563_ = v___y_2754_;
v___y_2564_ = v___y_2757_;
v___y_2565_ = v_decl_2748_;
v___y_2566_ = v___y_2756_;
v___y_2567_ = v___y_2753_;
v___y_2568_ = v___y_2747_;
goto v___jp_2558_;
}
}
}
v___jp_2791_:
{
lean_object* v_fvarId_2803_; lean_object* v_type_2804_; lean_object* v_value_2805_; lean_object* v___x_2806_; 
v_fvarId_2803_ = lean_ctor_get(v___y_2793_, 0);
v_type_2804_ = lean_ctor_get(v___y_2793_, 2);
v_value_2805_ = lean_ctor_get(v___y_2793_, 3);
lean_inc(v_value_2805_);
v___x_2806_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2805_, v___y_2796_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
if (lean_obj_tag(v_a_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v___x_2809_; 
v_val_2808_ = lean_ctor_get(v_a_2807_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_a_2807_, 1);
v___x_2809_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2797_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2794_, v___y_2793_, v_val_2808_, v___y_2800_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v_fvarId_2812_; lean_object* v_type_2813_; lean_object* v_value_2814_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v_fvarId_2812_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_fvarId_2812_);
v_type_2813_ = lean_ctor_get(v_a_2811_, 2);
lean_inc_ref(v_type_2813_);
v_value_2814_ = lean_ctor_get(v_a_2811_, 3);
lean_inc(v_value_2814_);
v___y_2745_ = v___y_2792_;
v___y_2746_ = v___y_2794_;
v___y_2747_ = v___y_2795_;
v_decl_2748_ = v_a_2811_;
v_fvarId_2749_ = v_fvarId_2812_;
v_type_2750_ = v_type_2813_;
v_value_2751_ = v_value_2814_;
v___y_2752_ = v___y_2796_;
v___y_2753_ = v___y_2797_;
v___y_2754_ = v___y_2798_;
v___y_2755_ = v___y_2799_;
v___y_2756_ = v___y_2800_;
v___y_2757_ = v___y_2801_;
v___y_2758_ = v___y_2802_;
goto v___jp_2744_;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_code_2358_);
v_a_2815_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2810_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2810_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_val_2808_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_code_2358_);
v_a_2823_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2809_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2809_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_inc(v_value_2805_);
lean_inc_ref(v_type_2804_);
lean_inc(v_fvarId_2803_);
lean_dec(v_a_2807_);
v___y_2745_ = v___y_2792_;
v___y_2746_ = v___y_2794_;
v___y_2747_ = v___y_2795_;
v_decl_2748_ = v___y_2793_;
v_fvarId_2749_ = v_fvarId_2803_;
v_type_2750_ = v_type_2804_;
v_value_2751_ = v_value_2805_;
v___y_2752_ = v___y_2796_;
v___y_2753_ = v___y_2797_;
v___y_2754_ = v___y_2798_;
v___y_2755_ = v___y_2799_;
v___y_2756_ = v___y_2800_;
v___y_2757_ = v___y_2801_;
v___y_2758_ = v___y_2802_;
goto v___jp_2744_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_code_2358_);
v_a_2831_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2806_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2806_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
v___jp_2839_:
{
if (v___y_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v_code_2358_);
v___x_2843_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___y_2841_);
lean_ctor_set(v___x_2843_, 1, v___y_2840_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; 
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_code_2358_);
return v___x_2845_;
}
}
v___jp_2846_:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Lean_instBEqFVarId_beq(v___y_2850_, v___y_2849_);
lean_dec(v___y_2850_);
if (v___x_2851_ == 0)
{
lean_dec_ref(v___y_2848_);
v___y_2840_ = v___y_2847_;
v___y_2841_ = v___y_2849_;
v___y_2842_ = v___x_2851_;
goto v___jp_2839_;
}
else
{
size_t v___x_2852_; size_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2852_ = lean_ptr_addr(v___y_2848_);
lean_dec_ref(v___y_2848_);
v___x_2853_ = lean_ptr_addr(v___y_2847_);
v___x_2854_ = lean_usize_dec_eq(v___x_2852_, v___x_2853_);
v___y_2840_ = v___y_2847_;
v___y_2841_ = v___y_2849_;
v___y_2842_ = v___x_2854_;
goto v___jp_2839_;
}
}
v___jp_2855_:
{
if (lean_obj_tag(v___y_2860_) == 0)
{
lean_dec_ref_known(v___y_2860_, 1);
v___y_2847_ = v___y_2856_;
v___y_2848_ = v___y_2857_;
v___y_2849_ = v___y_2858_;
v___y_2850_ = v___y_2859_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec_ref(v_code_2358_);
v_a_2861_ = lean_ctor_get(v___y_2860_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___y_2860_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___y_2860_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___y_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
v___jp_2869_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2880_; 
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2881_);
v___x_2874_ = v___x_2872_;
v_isShared_2875_ = v_isSharedCheck_2880_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v___x_2872_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2880_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___y_2870_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2876_);
v___x_2878_ = v___x_2874_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v___y_2870_);
v_a_2882_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2872_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2872_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
v___jp_2890_:
{
if (lean_obj_tag(v___y_2893_) == 0)
{
lean_dec_ref_known(v___y_2893_, 1);
v___y_2870_ = v___y_2891_;
v___y_2871_ = v___y_2892_;
goto v___jp_2869_;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v___y_2891_);
v_a_2894_ = lean_ctor_get(v___y_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___y_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___y_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___y_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
v___jp_2902_:
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_nat_dec_lt(v___y_2908_, v___y_2904_);
lean_dec(v___y_2908_);
if (v___x_2912_ == 0)
{
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
v___y_2870_ = v___y_2907_;
v___y_2871_ = v___y_2909_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = lean_box(0);
v___x_2914_ = lean_nat_dec_le(v___y_2904_, v___y_2904_);
if (v___x_2914_ == 0)
{
if (v___x_2912_ == 0)
{
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
v___y_2870_ = v___y_2907_;
v___y_2871_ = v___y_2909_;
goto v___jp_2869_;
}
else
{
size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = ((size_t)0ULL);
v___x_2916_ = lean_usize_of_nat(v___y_2904_);
lean_dec(v___y_2904_);
v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2903_, v___x_2915_, v___x_2916_, v___x_2913_, v___y_2905_, v___y_2906_, v___y_2910_, v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v___y_2903_);
v___y_2891_ = v___y_2907_;
v___y_2892_ = v___y_2909_;
v___y_2893_ = v___x_2917_;
goto v___jp_2890_;
}
}
else
{
size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = ((size_t)0ULL);
v___x_2919_ = lean_usize_of_nat(v___y_2904_);
lean_dec(v___y_2904_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2903_, v___x_2918_, v___x_2919_, v___x_2913_, v___y_2905_, v___y_2906_, v___y_2910_, v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v___y_2903_);
v___y_2891_ = v___y_2907_;
v___y_2892_ = v___y_2909_;
v___y_2893_ = v___x_2920_;
goto v___jp_2890_;
}
}
}
v___jp_2921_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2926_, 0, v___y_2925_);
lean_ctor_set(v___x_2926_, 1, v___y_2924_);
lean_ctor_set(v___x_2926_, 2, v___y_2922_);
lean_ctor_set(v___x_2926_, 3, v___y_2923_);
v___x_2927_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
v___jp_2929_:
{
if (v___y_2935_ == 0)
{
lean_dec(v___y_2934_);
lean_dec_ref(v_code_2358_);
v___y_2922_ = v___y_2930_;
v___y_2923_ = v___y_2931_;
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2932_;
goto v___jp_2921_;
}
else
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_instBEqFVarId_beq(v___y_2934_, v___y_2930_);
lean_dec(v___y_2934_);
if (v___x_2936_ == 0)
{
lean_dec_ref(v_code_2358_);
v___y_2922_ = v___y_2930_;
v___y_2923_ = v___y_2931_;
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2932_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2937_; 
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_code_2358_);
return v___x_2937_;
}
}
}
v___jp_2938_:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_array_get_size(v___y_2940_);
v___x_2953_ = lean_nat_dec_lt(v___y_2942_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2358_);
v___y_2903_ = v___y_2940_;
v___y_2904_ = v___x_2952_;
v___y_2905_ = v___y_2948_;
v___y_2906_ = v___y_2949_;
v___y_2907_ = v___y_2943_;
v___y_2908_ = v___y_2942_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2950_;
v___y_2911_ = v___y_2951_;
goto v___jp_2902_;
}
else
{
if (v___x_2953_ == 0)
{
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2358_);
v___y_2903_ = v___y_2940_;
v___y_2904_ = v___x_2952_;
v___y_2905_ = v___y_2948_;
v___y_2906_ = v___y_2949_;
v___y_2907_ = v___y_2943_;
v___y_2908_ = v___y_2942_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2950_;
v___y_2911_ = v___y_2951_;
goto v___jp_2902_;
}
else
{
size_t v___x_2954_; size_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = lean_usize_of_nat(v___x_2952_);
v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2940_, v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2358_);
v___y_2903_ = v___y_2940_;
v___y_2904_ = v___x_2952_;
v___y_2905_ = v___y_2948_;
v___y_2906_ = v___y_2949_;
v___y_2907_ = v___y_2943_;
v___y_2908_ = v___y_2942_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2950_;
v___y_2911_ = v___y_2951_;
goto v___jp_2902_;
}
else
{
lean_object* v___x_2957_; 
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2942_);
lean_inc(v___y_2939_);
v___x_2957_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2939_, v___y_2947_);
if (lean_obj_tag(v___x_2957_) == 0)
{
size_t v___x_2958_; size_t v___x_2959_; uint8_t v___x_2960_; 
lean_dec_ref_known(v___x_2957_, 1);
v___x_2958_ = lean_ptr_addr(v___y_2944_);
lean_dec_ref(v___y_2944_);
v___x_2959_ = lean_ptr_addr(v___y_2940_);
v___x_2960_ = lean_usize_dec_eq(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___y_2946_);
v___y_2930_ = v___y_2939_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v___y_2943_;
v___y_2934_ = v___y_2945_;
v___y_2935_ = v___x_2960_;
goto v___jp_2929_;
}
else
{
size_t v___x_2961_; size_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = lean_ptr_addr(v___y_2946_);
lean_dec_ref(v___y_2946_);
v___x_2962_ = lean_ptr_addr(v___y_2943_);
v___x_2963_ = lean_usize_dec_eq(v___x_2961_, v___x_2962_);
v___y_2930_ = v___y_2939_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v___y_2943_;
v___y_2934_ = v___y_2945_;
v___y_2935_ = v___x_2963_;
goto v___jp_2929_;
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2358_);
v_a_2964_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2957_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2957_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
}
v___jp_2972_:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2974_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2983_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___y_2973_);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___y_2973_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___y_2973_);
v_a_2984_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2975_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2975_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v___jp_2992_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_dec_ref_known(v___y_2995_, 1);
v___y_2973_ = v___y_2993_;
v___y_2974_ = v___y_2994_;
goto v___jp_2972_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___y_2993_);
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___y_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___y_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___y_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
v___jp_3004_:
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_nat_dec_lt(v___y_3008_, v___y_3009_);
lean_dec(v___y_3008_);
if (v___x_3011_ == 0)
{
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3007_);
v___y_2973_ = v___y_3006_;
v___y_2974_ = v___y_3010_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_nat_dec_le(v___y_3009_, v___y_3009_);
if (v___x_3013_ == 0)
{
if (v___x_3011_ == 0)
{
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3007_);
v___y_2973_ = v___y_3006_;
v___y_2974_ = v___y_3010_;
goto v___jp_2972_;
}
else
{
size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = lean_usize_of_nat(v___y_3009_);
lean_dec(v___y_3009_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3007_, v___x_3014_, v___x_3015_, v___x_3012_, v___y_3005_);
lean_dec_ref(v___y_3007_);
v___y_2993_ = v___y_3006_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___x_3016_;
goto v___jp_2992_;
}
}
else
{
size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = lean_usize_of_nat(v___y_3009_);
lean_dec(v___y_3009_);
v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3007_, v___x_3017_, v___x_3018_, v___x_3012_, v___y_3005_);
lean_dec_ref(v___y_3007_);
v___y_2993_ = v___y_3006_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___x_3019_;
goto v___jp_2992_;
}
}
}
v___jp_3020_:
{
switch(lean_obj_tag(v_code_2358_))
{
case 0:
{
lean_object* v_decl_3028_; lean_object* v_k_3029_; uint8_t v___x_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; 
v_decl_3028_ = lean_ctor_get(v_code_2358_, 0);
v_k_3029_ = lean_ctor_get(v_code_2358_, 1);
v___x_3030_ = 0;
v___x_3031_ = 0;
lean_inc_ref(v_decl_3028_);
v___x_3032_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3030_, v___x_3031_, v_decl_3028_, v___y_3022_, v___y_3025_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3030_, v_decl_3028_, v_a_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3022_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
lean_inc_ref(v_k_3029_);
lean_inc_ref(v_decl_3028_);
v___y_2792_ = v_decl_3028_;
v___y_2793_ = v_a_3033_;
v___y_2794_ = v___x_3030_;
v___y_2795_ = v_k_3029_;
v___y_2796_ = v___y_3021_;
v___y_2797_ = v___y_3022_;
v___y_2798_ = v___y_3023_;
v___y_2799_ = v___y_3024_;
v___y_2800_ = v___y_3025_;
v___y_2801_ = v___y_3026_;
v___y_2802_ = v___y_3027_;
goto v___jp_2791_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_3033_);
lean_dec_ref_known(v_code_2358_, 2);
lean_dec_ref(v___y_3026_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
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
else
{
lean_inc_ref(v_k_3029_);
lean_inc_ref(v_decl_3028_);
v___y_2792_ = v_decl_3028_;
v___y_2793_ = v_a_3033_;
v___y_2794_ = v___x_3030_;
v___y_2795_ = v_k_3029_;
v___y_2796_ = v___y_3021_;
v___y_2797_ = v___y_3022_;
v___y_2798_ = v___y_3023_;
v___y_2799_ = v___y_3024_;
v___y_2800_ = v___y_3025_;
v___y_2801_ = v___y_3026_;
v___y_2802_ = v___y_3027_;
goto v___jp_2791_;
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref_known(v_code_2358_, 2);
lean_dec_ref(v___y_3026_);
v_a_3044_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3032_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3032_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3052_; lean_object* v_args_3053_; lean_object* v___x_3054_; lean_object* v_subst_3055_; uint8_t v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v_fvarId_3052_ = lean_ctor_get(v_code_2358_, 0);
v_args_3053_ = lean_ctor_get(v_code_2358_, 1);
v___x_3054_ = lean_st_ref_get(v___y_3022_);
v_subst_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_subst_3055_);
lean_dec(v___x_3054_);
v___x_3056_ = 0;
v___x_3057_ = 0;
lean_inc(v_fvarId_3052_);
v___x_3058_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3055_, v_fvarId_3052_, v___x_3057_);
lean_dec_ref(v_subst_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_fvarId_3059_; lean_object* v___x_3060_; 
v_fvarId_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_fvarId_3059_);
lean_dec_ref_known(v___x_3058_, 1);
lean_inc_ref(v_args_3053_);
v___x_3060_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3056_, v___x_3057_, v_args_3053_, v___y_3022_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc_n(v_a_3061_, 2);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3059_, v_a_3061_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
if (lean_obj_tag(v_a_3063_) == 1)
{
lean_object* v_val_3064_; 
lean_dec(v_a_3061_);
lean_dec(v_fvarId_3059_);
lean_dec_ref_known(v_code_2358_, 2);
v_val_3064_ = lean_ctor_get(v_a_3063_, 0);
lean_inc(v_val_3064_);
lean_dec_ref_known(v_a_3063_, 1);
v_code_2358_ = v_val_3064_;
v_a_2359_ = v___y_3021_;
v_a_2360_ = v___y_3022_;
v_a_2361_ = v___y_3023_;
v_a_2362_ = v___y_3024_;
v_a_2363_ = v___y_3025_;
v_a_2364_ = v___y_3026_;
v_a_2365_ = v___y_3027_;
goto _start;
}
else
{
lean_object* v___x_3066_; 
lean_dec(v_a_3063_);
lean_dec_ref(v___y_3026_);
lean_inc(v_fvarId_3059_);
v___x_3066_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3059_, v___y_3022_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
lean_dec_ref_known(v___x_3066_, 1);
v___x_3067_ = lean_unsigned_to_nat(0u);
v___x_3068_ = lean_array_get_size(v_a_3061_);
v___x_3069_ = lean_nat_dec_lt(v___x_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_inc(v_fvarId_3052_);
lean_inc_ref(v_args_3053_);
v___y_2847_ = v_a_3061_;
v___y_2848_ = v_args_3053_;
v___y_2849_ = v_fvarId_3059_;
v___y_2850_ = v_fvarId_3052_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_nat_dec_le(v___x_3068_, v___x_3068_);
if (v___x_3071_ == 0)
{
if (v___x_3069_ == 0)
{
lean_inc(v_fvarId_3052_);
lean_inc_ref(v_args_3053_);
v___y_2847_ = v_a_3061_;
v___y_2848_ = v_args_3053_;
v___y_2849_ = v_fvarId_3059_;
v___y_2850_ = v_fvarId_3052_;
goto v___jp_2846_;
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = lean_usize_of_nat(v___x_3068_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3061_, v___x_3072_, v___x_3073_, v___x_3070_, v___y_3022_);
lean_inc(v_fvarId_3052_);
lean_inc_ref(v_args_3053_);
v___y_2856_ = v_a_3061_;
v___y_2857_ = v_args_3053_;
v___y_2858_ = v_fvarId_3059_;
v___y_2859_ = v_fvarId_3052_;
v___y_2860_ = v___x_3074_;
goto v___jp_2855_;
}
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = lean_usize_of_nat(v___x_3068_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3061_, v___x_3075_, v___x_3076_, v___x_3070_, v___y_3022_);
lean_inc(v_fvarId_3052_);
lean_inc_ref(v_args_3053_);
v___y_2856_ = v_a_3061_;
v___y_2857_ = v_args_3053_;
v___y_2858_ = v_fvarId_3059_;
v___y_2859_ = v_fvarId_3052_;
v___y_2860_ = v___x_3077_;
goto v___jp_2855_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3061_);
lean_dec(v_fvarId_3059_);
lean_dec_ref_known(v_code_2358_, 2);
v_a_3078_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3066_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3066_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3061_);
lean_dec(v_fvarId_3059_);
lean_dec_ref_known(v_code_2358_, 2);
lean_dec_ref(v___y_3026_);
v_a_3086_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3062_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3062_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_fvarId_3059_);
lean_dec_ref_known(v_code_2358_, 2);
lean_dec_ref(v___y_3026_);
v_a_3094_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3060_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3060_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3102_; 
lean_dec_ref_known(v_code_2358_, 2);
v___x_3102_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3056_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec_ref(v___y_3026_);
return v___x_3102_;
}
}
case 4:
{
lean_object* v_cases_3103_; lean_object* v___x_3104_; 
v_cases_3103_ = lean_ctor_get(v_code_2358_, 0);
lean_inc_ref(v_cases_3103_);
v___x_3104_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3103_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3177_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3177_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3177_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
if (lean_obj_tag(v_a_3105_) == 1)
{
lean_object* v_val_3109_; lean_object* v___x_3111_; 
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_val_3109_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_val_3109_);
lean_dec_ref_known(v_a_3105_, 1);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v_val_3109_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_val_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v_typeName_3113_; lean_object* v_resultType_3114_; lean_object* v_discr_3115_; lean_object* v_alts_3116_; lean_object* v___x_3117_; lean_object* v_subst_3118_; uint8_t v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; 
lean_del_object(v___x_3107_);
lean_dec(v_a_3105_);
v_typeName_3113_ = lean_ctor_get(v_cases_3103_, 0);
v_resultType_3114_ = lean_ctor_get(v_cases_3103_, 1);
v_discr_3115_ = lean_ctor_get(v_cases_3103_, 2);
v_alts_3116_ = lean_ctor_get(v_cases_3103_, 3);
v___x_3117_ = lean_st_ref_get(v___y_3022_);
v_subst_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc_ref(v_subst_3118_);
lean_dec(v___x_3117_);
v___x_3119_ = 0;
v___x_3120_ = 0;
lean_inc(v_discr_3115_);
v___x_3121_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3118_, v_discr_3115_, v___x_3120_);
lean_dec_ref(v_subst_3118_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_fvarId_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_fvarId_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc_n(v_fvarId_3122_, 2);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = lean_st_ref_get(v___y_3022_);
v___x_3124_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3116_);
v___x_3125_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3122_, v___x_3124_, v_alts_3116_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3127_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3126_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3159_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_subst_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_subst_3132_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_subst_3132_);
lean_dec(v___x_3123_);
lean_inc_ref(v_resultType_3114_);
v___x_3133_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3119_, v_subst_3132_, v___x_3120_, v_resultType_3114_);
lean_dec_ref(v_subst_3132_);
v___x_3134_ = lean_array_get_size(v_a_3128_);
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_dec_eq(v___x_3134_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_del_object(v___x_3130_);
lean_inc_ref(v_resultType_3114_);
lean_inc(v_discr_3115_);
lean_inc_ref(v_alts_3116_);
lean_inc(v_typeName_3113_);
v___y_2939_ = v_fvarId_3122_;
v___y_2940_ = v_a_3128_;
v___y_2941_ = v_typeName_3113_;
v___y_2942_ = v___x_3124_;
v___y_2943_ = v___x_3133_;
v___y_2944_ = v_alts_3116_;
v___y_2945_ = v_discr_3115_;
v___y_2946_ = v_resultType_3114_;
v___y_2947_ = v___y_3022_;
v___y_2948_ = v___y_3024_;
v___y_2949_ = v___y_3025_;
v___y_2950_ = v___y_3026_;
v___y_2951_ = v___y_3027_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_array_fget_borrowed(v_a_3128_, v___x_3124_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_params_3138_; lean_object* v_code_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
lean_del_object(v___x_3130_);
v_params_3138_ = lean_ctor_get(v___x_3137_, 1);
v_code_3139_ = lean_ctor_get(v___x_3137_, 2);
v___x_3140_ = lean_array_get_size(v_params_3138_);
v___x_3141_ = lean_nat_dec_lt(v___x_3124_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_inc_ref(v_code_3139_);
lean_inc_ref(v_params_3138_);
lean_dec_ref(v___x_3133_);
lean_dec(v_a_3128_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v___y_3005_ = v___y_3025_;
v___y_3006_ = v_code_3139_;
v___y_3007_ = v_params_3138_;
v___y_3008_ = v___x_3124_;
v___y_3009_ = v___x_3140_;
v___y_3010_ = v___y_3022_;
goto v___jp_3004_;
}
else
{
if (v___x_3141_ == 0)
{
lean_inc_ref(v_code_3139_);
lean_inc_ref(v_params_3138_);
lean_dec_ref(v___x_3133_);
lean_dec(v_a_3128_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v___y_3005_ = v___y_3025_;
v___y_3006_ = v_code_3139_;
v___y_3007_ = v_params_3138_;
v___y_3008_ = v___x_3124_;
v___y_3009_ = v___x_3140_;
v___y_3010_ = v___y_3022_;
goto v___jp_3004_;
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = lean_usize_of_nat(v___x_3140_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3138_, v___x_3142_, v___x_3143_, v___y_3022_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; uint8_t v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
if (v___x_3146_ == 0)
{
lean_inc_ref(v_code_3139_);
lean_inc_ref(v_params_3138_);
lean_dec_ref(v___x_3133_);
lean_dec(v_a_3128_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v___y_3005_ = v___y_3025_;
v___y_3006_ = v_code_3139_;
v___y_3007_ = v_params_3138_;
v___y_3008_ = v___x_3124_;
v___y_3009_ = v___x_3140_;
v___y_3010_ = v___y_3022_;
goto v___jp_3004_;
}
else
{
lean_inc_ref(v_resultType_3114_);
lean_inc(v_discr_3115_);
lean_inc_ref(v_alts_3116_);
lean_inc(v_typeName_3113_);
v___y_2939_ = v_fvarId_3122_;
v___y_2940_ = v_a_3128_;
v___y_2941_ = v_typeName_3113_;
v___y_2942_ = v___x_3124_;
v___y_2943_ = v___x_3133_;
v___y_2944_ = v_alts_3116_;
v___y_2945_ = v_discr_3115_;
v___y_2946_ = v_resultType_3114_;
v___y_2947_ = v___y_3022_;
v___y_2948_ = v___y_3024_;
v___y_2949_ = v___y_3025_;
v___y_2950_ = v___y_3026_;
v___y_2951_ = v___y_3027_;
goto v___jp_2938_;
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v___x_3133_);
lean_dec(v_a_3128_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_a_3147_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3144_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3144_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
else
{
lean_object* v_code_3155_; lean_object* v___x_3157_; 
lean_inc_ref(v___x_3137_);
lean_dec_ref(v___x_3133_);
lean_dec(v_a_3128_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_code_3155_ = lean_ctor_get(v___x_3137_, 0);
lean_inc_ref(v_code_3155_);
lean_dec_ref_known(v___x_3137_, 1);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_code_3155_);
v___x_3157_ = v___x_3130_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_code_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___x_3123_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_a_3160_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3127_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3127_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v___x_3123_);
lean_dec(v_fvarId_3122_);
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_a_3168_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3125_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3125_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3176_; 
lean_dec_ref_known(v_code_2358_, 1);
v___x_3176_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3119_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec_ref(v___y_3026_);
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref_known(v_code_2358_, 1);
lean_dec_ref(v___y_3026_);
v_a_3178_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3104_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3104_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3186_; lean_object* v___x_3187_; lean_object* v_subst_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; 
v_fvarId_3186_ = lean_ctor_get(v_code_2358_, 0);
v___x_3187_ = lean_st_ref_get(v___y_3022_);
v_subst_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_ref(v_subst_3188_);
lean_dec(v___x_3187_);
v___x_3189_ = 0;
lean_inc(v_fvarId_3186_);
v___x_3190_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3188_, v_fvarId_3186_, v___x_3189_);
lean_dec_ref(v_subst_3188_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_fvarId_3191_; lean_object* v___x_3192_; 
lean_dec_ref(v___y_3026_);
v_fvarId_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_n(v_fvarId_3191_, 2);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3191_, v___y_3022_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3211_; 
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v___x_3192_, 0);
lean_dec(v_unused_3212_);
v___x_3194_ = v___x_3192_;
v_isShared_3195_ = v_isSharedCheck_3211_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v___x_3192_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3211_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
uint8_t v___x_3196_; 
v___x_3196_ = l_Lean_instBEqFVarId_beq(v_fvarId_3186_, v_fvarId_3191_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3206_; 
v_isSharedCheck_3206_ = !lean_is_exclusive(v_code_2358_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v_code_2358_, 0);
lean_dec(v_unused_3207_);
v___x_3198_ = v_code_2358_;
v_isShared_3199_ = v_isSharedCheck_3206_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v_code_2358_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3206_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v_fvarId_3191_);
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_fvarId_3191_);
v___x_3201_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3201_);
v___x_3203_ = v___x_3194_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v___x_3209_; 
lean_dec(v_fvarId_3191_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v_code_2358_);
v___x_3209_ = v___x_3194_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_code_2358_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_fvarId_3191_);
lean_dec_ref_known(v_code_2358_, 1);
v_a_3213_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3192_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3192_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
uint8_t v___x_3221_; lean_object* v___x_3222_; 
lean_dec_ref_known(v_code_2358_, 1);
v___x_3221_ = 0;
v___x_3222_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3221_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec_ref(v___y_3026_);
return v___x_3222_;
}
}
case 6:
{
lean_object* v_type_3223_; lean_object* v___x_3224_; lean_object* v_subst_3225_; uint8_t v___x_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; size_t v___x_3229_; size_t v___x_3230_; uint8_t v___x_3231_; 
lean_dec_ref(v___y_3026_);
v_type_3223_ = lean_ctor_get(v_code_2358_, 0);
v___x_3224_ = lean_st_ref_get(v___y_3022_);
v_subst_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_subst_3225_);
lean_dec(v___x_3224_);
v___x_3226_ = 0;
v___x_3227_ = 0;
lean_inc_ref(v_type_3223_);
v___x_3228_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3226_, v_subst_3225_, v___x_3227_, v_type_3223_);
lean_dec_ref(v_subst_3225_);
v___x_3229_ = lean_ptr_addr(v_type_3223_);
v___x_3230_ = lean_ptr_addr(v___x_3228_);
v___x_3231_ = lean_usize_dec_eq(v___x_3229_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3239_; 
v_isSharedCheck_3239_ = !lean_is_exclusive(v_code_2358_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_code_2358_, 0);
lean_dec(v_unused_3240_);
v___x_3233_ = v_code_2358_;
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v_code_2358_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3228_);
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3228_);
v___x_3236_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
}
}
else
{
lean_object* v___x_3241_; 
lean_dec_ref(v___x_3228_);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v_code_2358_);
return v___x_3241_;
}
}
default: 
{
lean_object* v_decl_3242_; lean_object* v_k_3243_; 
v_decl_3242_ = lean_ctor_get(v_code_2358_, 0);
v_k_3243_ = lean_ctor_get(v_code_2358_, 1);
lean_inc_ref(v_k_3243_);
lean_inc_ref(v_decl_3242_);
v_decl_2476_ = v_decl_3242_;
v_k_2477_ = v_k_3243_;
v___y_2478_ = v___y_3021_;
v___y_2479_ = v___y_3022_;
v___y_2480_ = v___y_3023_;
v___y_2481_ = v___y_3024_;
v___y_2482_ = v___y_3025_;
v___y_2483_ = v___y_3026_;
v___y_2484_ = v___y_3027_;
goto v___jp_2475_;
}
}
}
v___jp_3260_:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2360_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3262_; lean_object* v_visited_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
lean_dec_ref_known(v___x_3261_, 1);
v___x_3262_ = lean_st_ref_get(v_a_2360_);
v_visited_3263_ = lean_ctor_get(v___x_3262_, 4);
lean_inc(v_visited_3263_);
lean_dec(v___x_3262_);
v___x_3264_ = lean_unsigned_to_nat(1u);
v___x_3265_ = lean_nat_add(v_currRecDepth_3247_, v___x_3264_);
lean_dec(v_currRecDepth_3247_);
v___x_3266_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3266_, 0, v_fileName_3244_);
lean_ctor_set(v___x_3266_, 1, v_fileMap_3245_);
lean_ctor_set(v___x_3266_, 2, v_options_3246_);
lean_ctor_set(v___x_3266_, 3, v___x_3265_);
lean_ctor_set(v___x_3266_, 4, v_maxRecDepth_3248_);
lean_ctor_set(v___x_3266_, 5, v_ref_3249_);
lean_ctor_set(v___x_3266_, 6, v_currNamespace_3250_);
lean_ctor_set(v___x_3266_, 7, v_openDecls_3251_);
lean_ctor_set(v___x_3266_, 8, v_initHeartbeats_3252_);
lean_ctor_set(v___x_3266_, 9, v_maxHeartbeats_3253_);
lean_ctor_set(v___x_3266_, 10, v_quotContext_3254_);
lean_ctor_set(v___x_3266_, 11, v_currMacroScope_3255_);
lean_ctor_set(v___x_3266_, 12, v_cancelTk_x3f_3257_);
lean_ctor_set(v___x_3266_, 13, v_inheritedTraceOptions_3259_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*14, v_diag_3256_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*14 + 1, v_suppressElabErrors_3258_);
v___x_3267_ = lean_unsigned_to_nat(128u);
v___x_3268_ = lean_nat_mod(v_visited_3263_, v___x_3267_);
lean_dec(v_visited_3263_);
v___x_3269_ = lean_unsigned_to_nat(0u);
v___x_3270_ = lean_nat_dec_eq(v___x_3268_, v___x_3269_);
lean_dec(v___x_3268_);
if (v___x_3270_ == 0)
{
v___y_3021_ = v_a_2359_;
v___y_3022_ = v_a_2360_;
v___y_3023_ = v_a_2361_;
v___y_3024_ = v_a_2362_;
v___y_3025_ = v_a_2363_;
v___y_3026_ = v___x_3266_;
v___y_3027_ = v_a_2365_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3272_ = l_Lean_Core_checkSystem(v___x_3271_, v___x_3266_, v_a_2365_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref_known(v___x_3272_, 1);
v___y_3021_ = v_a_2359_;
v___y_3022_ = v_a_2360_;
v___y_3023_ = v_a_2361_;
v___y_3024_ = v_a_2362_;
v___y_3025_ = v_a_2363_;
v___y_3026_ = v___x_3266_;
v___y_3027_ = v_a_2365_;
goto v___jp_3020_;
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec_ref_known(v___x_3266_, 14);
lean_dec_ref(v_code_2358_);
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_inheritedTraceOptions_3259_);
lean_dec(v_cancelTk_x3f_3257_);
lean_dec(v_currMacroScope_3255_);
lean_dec(v_quotContext_3254_);
lean_dec(v_maxHeartbeats_3253_);
lean_dec(v_initHeartbeats_3252_);
lean_dec(v_openDecls_3251_);
lean_dec(v_currNamespace_3250_);
lean_dec(v_ref_3249_);
lean_dec(v_maxRecDepth_3248_);
lean_dec(v_currRecDepth_3247_);
lean_dec_ref(v_options_3246_);
lean_dec_ref(v_fileMap_3245_);
lean_dec_ref(v_fileName_3244_);
lean_dec_ref(v_code_2358_);
v_a_3281_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3261_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3261_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_params_3302_; lean_object* v_type_3303_; lean_object* v_value_3304_; lean_object* v___x_3305_; lean_object* v_subst_3306_; uint8_t v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_params_3302_ = lean_ctor_get(v_decl_3293_, 2);
v_type_3303_ = lean_ctor_get(v_decl_3293_, 3);
v_value_3304_ = lean_ctor_get(v_decl_3293_, 4);
v___x_3305_ = lean_st_ref_get(v_a_3295_);
v_subst_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc_ref(v_subst_3306_);
lean_dec(v___x_3305_);
v___x_3307_ = 0;
v___x_3308_ = 0;
lean_inc_ref(v_type_3303_);
v___x_3309_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3307_, v_subst_3306_, v___x_3308_, v_type_3303_);
lean_dec_ref(v_subst_3306_);
lean_inc_ref(v_params_3302_);
v___x_3310_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3307_, v___x_3308_, v_params_3302_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
lean_inc_ref(v_a_3299_);
lean_inc_ref(v_value_3304_);
v___x_3312_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3304_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3307_, v_decl_3293_, v___x_3309_, v_a_3311_, v_a_3313_, v_a_3298_);
return v___x_3314_;
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v_a_3311_);
lean_dec_ref(v___x_3309_);
lean_dec_ref(v_decl_3293_);
v_a_3315_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3312_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3312_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v___x_3309_);
lean_dec_ref(v_decl_3293_);
v_a_3323_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3310_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3310_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3341_, lean_object* v_i_3342_, lean_object* v_as_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3341_, v_i_3342_, v_as_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3363_, lean_object* v_k_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3363_, v_k_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3384_, uint8_t v_t_3385_, lean_object* v_decl_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3384_, v_t_3385_, v_decl_3386_, v___y_3388_, v___y_3391_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3396_, lean_object* v_t_3397_, lean_object* v_decl_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
uint8_t v_pu_boxed_3407_; uint8_t v_t_boxed_3408_; lean_object* v_res_3409_; 
v_pu_boxed_3407_ = lean_unbox(v_pu_3396_);
v_t_boxed_3408_ = lean_unbox(v_t_3397_);
v_res_3409_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3407_, v_t_boxed_3408_, v_decl_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3410_, uint8_t v_t_3411_, lean_object* v_args_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3410_, v_t_3411_, v_args_3412_, v___y_3414_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3422_, lean_object* v_t_3423_, lean_object* v_args_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v_pu_boxed_3433_; uint8_t v_t_boxed_3434_; lean_object* v_res_3435_; 
v_pu_boxed_3433_ = lean_unbox(v_pu_3422_);
v_t_boxed_3434_ = lean_unbox(v_t_3423_);
v_res_3435_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3433_, v_t_boxed_3434_, v_args_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3436_, lean_object* v_R_3437_, lean_object* v_a_3438_, lean_object* v_b_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3438_, v_b_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3441_, lean_object* v_x_3442_, lean_object* v_x_3443_, lean_object* v_x_3444_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3442_, v_x_3443_, v_x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3446_, size_t v_i_3447_, size_t v_stop_3448_, lean_object* v_b_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3446_, v_i_3447_, v_stop_3448_, v_b_3449_, v___y_3451_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3459_, lean_object* v_i_3460_, lean_object* v_stop_3461_, lean_object* v_b_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
size_t v_i_boxed_3471_; size_t v_stop_boxed_3472_; lean_object* v_res_3473_; 
v_i_boxed_3471_ = lean_unbox_usize(v_i_3460_);
lean_dec(v_i_3460_);
v_stop_boxed_3472_ = lean_unbox_usize(v_stop_3461_);
lean_dec(v_stop_3461_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3459_, v_i_boxed_3471_, v_stop_boxed_3472_, v_b_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v_as_3459_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3474_, size_t v_i_3475_, size_t v_stop_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3474_, v_i_3475_, v_stop_3476_, v___y_3483_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3486_, lean_object* v_i_3487_, lean_object* v_stop_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
size_t v_i_boxed_3497_; size_t v_stop_boxed_3498_; lean_object* v_res_3499_; 
v_i_boxed_3497_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_stop_boxed_3498_ = lean_unbox_usize(v_stop_3488_);
lean_dec(v_stop_3488_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3486_, v_i_boxed_3497_, v_stop_boxed_3498_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v_as_3486_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3500_, size_t v_i_3501_, size_t v_stop_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3500_, v_i_3501_, v_stop_3502_, v_b_3503_, v___y_3505_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3510_, lean_object* v_i_3511_, lean_object* v_stop_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
size_t v_i_boxed_3519_; size_t v_stop_boxed_3520_; lean_object* v_res_3521_; 
v_i_boxed_3519_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_stop_boxed_3520_ = lean_unbox_usize(v_stop_3512_);
lean_dec(v_stop_3512_);
v_res_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3510_, v_i_boxed_3519_, v_stop_boxed_3520_, v_b_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_as_3510_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3522_, size_t v_i_3523_, size_t v_stop_3524_, lean_object* v_b_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3522_, v_i_3523_, v_stop_3524_, v_b_3525_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3535_, lean_object* v_i_3536_, lean_object* v_stop_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
size_t v_i_boxed_3547_; size_t v_stop_boxed_3548_; lean_object* v_res_3549_; 
v_i_boxed_3547_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_stop_boxed_3548_ = lean_unbox_usize(v_stop_3537_);
lean_dec(v_stop_3537_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3535_, v_i_boxed_3547_, v_stop_boxed_3548_, v_b_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v_as_3535_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3550_, size_t v_i_3551_, size_t v_stop_3552_, lean_object* v_b_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3550_, v_i_3551_, v_stop_3552_, v_b_3553_, v___y_3558_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3563_, lean_object* v_i_3564_, lean_object* v_stop_3565_, lean_object* v_b_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
size_t v_i_boxed_3575_; size_t v_stop_boxed_3576_; lean_object* v_res_3577_; 
v_i_boxed_3575_ = lean_unbox_usize(v_i_3564_);
lean_dec(v_i_3564_);
v_stop_boxed_3576_ = lean_unbox_usize(v_stop_3565_);
lean_dec(v_stop_3565_);
v_res_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3563_, v_i_boxed_3575_, v_stop_boxed_3576_, v_b_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec_ref(v_as_3563_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3578_, size_t v_i_3579_, size_t v_stop_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3578_, v_i_3579_, v_stop_3580_, v___y_3582_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3590_, lean_object* v_i_3591_, lean_object* v_stop_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
size_t v_i_boxed_3601_; size_t v_stop_boxed_3602_; lean_object* v_res_3603_; 
v_i_boxed_3601_ = lean_unbox_usize(v_i_3591_);
lean_dec(v_i_3591_);
v_stop_boxed_3602_ = lean_unbox_usize(v_stop_3592_);
lean_dec(v_stop_3592_);
v_res_3603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3590_, v_i_boxed_3601_, v_stop_boxed_3602_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v_as_3590_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3604_, size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3604_, v_sz_3605_, v_i_3606_, v_b_3607_, v___y_3609_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3617_, lean_object* v_sz_3618_, lean_object* v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3618_);
lean_dec(v_sz_3618_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3619_);
lean_dec(v_i_3619_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3617_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v_as_3617_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3632_, lean_object* v_x_3633_, size_t v_x_3634_, size_t v_x_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3633_, v_x_3634_, v_x_3635_, v_x_3636_, v_x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
size_t v_x_51412__boxed_3645_; size_t v_x_51413__boxed_3646_; lean_object* v_res_3647_; 
v_x_51412__boxed_3645_ = lean_unbox_usize(v_x_3641_);
lean_dec(v_x_3641_);
v_x_51413__boxed_3646_ = lean_unbox_usize(v_x_3642_);
lean_dec(v_x_3642_);
v_res_3647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3639_, v_x_3640_, v_x_51412__boxed_3645_, v_x_51413__boxed_3646_, v_x_3643_, v_x_3644_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3648_, uint8_t v_t_3649_, lean_object* v_i_3650_, lean_object* v_as_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3648_, v_t_3649_, v_i_3650_, v_as_3651_, v___y_3653_, v___y_3656_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3661_, lean_object* v_t_3662_, lean_object* v_i_3663_, lean_object* v_as_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_pu_boxed_3673_; uint8_t v_t_boxed_3674_; lean_object* v_res_3675_; 
v_pu_boxed_3673_ = lean_unbox(v_pu_3661_);
v_t_boxed_3674_ = lean_unbox(v_t_3662_);
v_res_3675_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3673_, v_t_boxed_3674_, v_i_3663_, v_as_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3676_, lean_object* v_n_3677_, lean_object* v_k_3678_, lean_object* v_v_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3677_, v_k_3678_, v_v_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3681_, size_t v_depth_3682_, lean_object* v_keys_3683_, lean_object* v_vals_3684_, lean_object* v_heq_3685_, lean_object* v_i_3686_, lean_object* v_entries_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3682_, v_keys_3683_, v_vals_3684_, v_i_3686_, v_entries_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3689_, lean_object* v_depth_3690_, lean_object* v_keys_3691_, lean_object* v_vals_3692_, lean_object* v_heq_3693_, lean_object* v_i_3694_, lean_object* v_entries_3695_){
_start:
{
size_t v_depth_boxed_3696_; lean_object* v_res_3697_; 
v_depth_boxed_3696_ = lean_unbox_usize(v_depth_3690_);
lean_dec(v_depth_3690_);
v_res_3697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3689_, v_depth_boxed_3696_, v_keys_3691_, v_vals_3692_, v_heq_3693_, v_i_3694_, v_entries_3695_);
lean_dec_ref(v_vals_3692_);
lean_dec_ref(v_keys_3691_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3698_, lean_object* v_x_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3699_, v_x_3700_, v_x_3701_, v_x_3702_);
return v___x_3703_;
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
