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
uint64_t lean_uint64_of_nat(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LCNF simp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_fvarId_629_; lean_object* v_type_630_; lean_object* v_declName_631_; lean_object* v_us_632_; lean_object* v_args_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_803_; 
v_fvarId_629_ = lean_ctor_get(v_letDecl_615_, 0);
v_type_630_ = lean_ctor_get(v_letDecl_615_, 2);
v_declName_631_ = lean_ctor_get(v_value_628_, 0);
v_us_632_ = lean_ctor_get(v_value_628_, 1);
v_args_633_ = lean_ctor_get(v_value_628_, 2);
v_isSharedCheck_803_ = !lean_is_exclusive(v_value_628_);
if (v_isSharedCheck_803_ == 0)
{
v___x_635_ = v_value_628_;
v_isShared_636_ = v_isSharedCheck_803_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_args_633_);
lean_inc(v_us_632_);
lean_inc(v_declName_631_);
lean_dec(v_value_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_803_;
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
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_792_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_792_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_792_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_792_;
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
lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_646_);
lean_inc(v_declName_631_);
v___x_653_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_631_, v_a_622_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_791_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_791_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_791_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_790_; 
v_val_658_ = lean_ctor_get(v_a_654_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_790_ == 0)
{
v___x_660_ = v_a_654_;
v_isShared_661_ = v_isSharedCheck_790_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v_a_654_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_790_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unbox(v_val_658_);
lean_dec(v_val_658_);
v___x_663_ = lean_bool_not(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_664_ = lean_box(0);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_664_);
v___x_666_ = v___x_656_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v___x_668_; 
lean_del_object(v___x_656_);
v___x_668_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_619_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_781_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_781_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_781_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_781_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unbox(v_a_669_);
lean_inc(v_declName_631_);
v___x_674_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_631_, v___x_673_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_772_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_772_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_772_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_772_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_771_; 
v_val_684_ = lean_ctor_get(v_a_675_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_771_ == 0)
{
v___x_686_ = v_a_675_;
v_isShared_687_ = v_isSharedCheck_771_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v_a_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_771_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unbox(v_a_669_);
lean_dec(v_a_669_);
v___x_689_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
lean_del_object(v___x_677_);
v___x_690_ = lean_array_get_size(v_args_633_);
v___x_691_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_684_);
lean_dec(v_val_684_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_del_object(v___x_686_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v___x_693_ = lean_box(0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_693_);
v___x_695_ = v___x_671_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_697_; 
lean_del_object(v___x_671_);
lean_inc_ref(v_type_630_);
v___x_697_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_689_, v_type_630_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; size_t v_sz_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc_n(v_a_698_, 2);
lean_dec_ref_known(v___x_697_, 1);
v_sz_699_ = lean_array_size(v_a_698_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_699_, v___x_700_, v_a_698_);
v___x_702_ = l_Array_append___redArg(v_args_633_, v___x_701_);
lean_dec_ref(v___x_701_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 2, v___x_702_);
v___x_704_ = v___x_635_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_declName_631_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_us_632_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___x_702_);
v___x_704_ = v_reuseFailAlloc_762_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_706_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_689_, v___x_704_, v___x_705_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v_fvarId_708_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v_fvarId_708_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_fvarId_708_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 5);
lean_ctor_set(v___x_660_, 0, v_fvarId_708_);
v___x_710_ = v___x_660_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_fvarId_708_);
v___x_710_ = v_reuseFailAlloc_753_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_a_707_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_713_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_698_, v___x_711_, v___x_712_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_fvarId_715_; lean_object* v___x_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v_fvarId_715_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_fvarId_715_);
lean_inc(v_fvarId_629_);
v___x_716_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_629_, v_fvarId_715_, v_a_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; 
lean_dec_ref_known(v___x_716_, 1);
v___x_717_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_615_, v_a_617_, v_a_620_);
lean_dec_ref(v_letDecl_615_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_727_; 
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_728_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_a_714_);
v___x_722_ = v___x_686_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_714_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_a_714_);
lean_del_object(v___x_686_);
v_a_729_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_717_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_717_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_a_714_);
lean_del_object(v___x_686_);
lean_dec_ref(v_letDecl_615_);
v_a_737_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_716_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_716_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_686_);
lean_dec_ref(v_letDecl_615_);
v_a_745_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_713_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_713_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_698_);
lean_del_object(v___x_686_);
lean_del_object(v___x_660_);
lean_dec_ref(v_letDecl_615_);
v_a_754_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_706_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_706_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_686_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_763_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_697_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_697_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
else
{
lean_del_object(v___x_686_);
lean_dec(v_val_684_);
lean_del_object(v___x_671_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_679_;
}
}
}
else
{
lean_dec(v_a_675_);
lean_del_object(v___x_671_);
lean_dec(v_a_669_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_box(0);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_671_);
lean_dec(v_a_669_);
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_773_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_674_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_674_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_660_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_782_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_668_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_668_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
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
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
v_a_793_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_643_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_643_);
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
lean_dec(v___x_640_);
lean_del_object(v___x_635_);
lean_dec_ref(v_args_633_);
lean_dec(v_us_632_);
lean_dec(v_declName_631_);
lean_dec_ref(v_letDecl_615_);
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
lean_dec(v_value_628_);
lean_dec_ref(v_letDecl_615_);
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
uint8_t v___x_24115__boxed_825_; size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v___x_24115__boxed_825_ = lean_unbox(v___x_821_);
v_sz_boxed_826_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_827_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24115__boxed_825_, v_sz_boxed_826_, v_i_boxed_827_, v_bs_824_);
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
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0(void){
_start:
{
uint8_t v___x_984_; uint8_t v___x_985_; 
v___x_984_ = 1;
v___x_985_ = lean_bool_not(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(uint8_t v___y_986_, lean_object* v_as_987_, size_t v_i_988_, size_t v_stop_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_eq(v_i_988_, v_stop_989_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; uint8_t v___y_993_; lean_object* v___y_998_; lean_object* v___x_1001_; 
v___x_991_ = 1;
v___x_1001_ = lean_array_uget_borrowed(v_as_987_, v_i_988_);
switch(lean_obj_tag(v___x_1001_))
{
case 0:
{
lean_object* v_code_1002_; 
v_code_1002_ = lean_ctor_get(v___x_1001_, 2);
v___y_998_ = v_code_1002_;
goto v___jp_997_;
}
case 1:
{
lean_object* v_code_1003_; 
v_code_1003_ = lean_ctor_get(v___x_1001_, 1);
v___y_998_ = v_code_1003_;
goto v___jp_997_;
}
default: 
{
lean_object* v_code_1004_; 
v_code_1004_ = lean_ctor_get(v___x_1001_, 0);
v___y_998_ = v_code_1004_;
goto v___jp_997_;
}
}
v___jp_992_:
{
if (v___y_993_ == 0)
{
size_t v___x_994_; size_t v___x_995_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_988_, v___x_994_);
v_i_988_ = v___x_995_;
goto _start;
}
else
{
return v___x_991_;
}
}
v___jp_997_:
{
if (lean_obj_tag(v___y_998_) == 6)
{
uint8_t v___x_999_; 
v___x_999_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___closed__0);
v___y_993_ = v___x_999_;
goto v___jp_992_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_bool_not(v___y_986_);
v___y_993_ = v___x_1000_;
goto v___jp_992_;
}
}
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = 0;
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v___y_1006_, lean_object* v_as_1007_, lean_object* v_i_1008_, lean_object* v_stop_1009_){
_start:
{
uint8_t v___y_46541__boxed_1010_; size_t v_i_boxed_1011_; size_t v_stop_boxed_1012_; uint8_t v_res_1013_; lean_object* v_r_1014_; 
v___y_46541__boxed_1010_ = lean_unbox(v___y_1006_);
v_i_boxed_1011_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_stop_boxed_1012_ = lean_unbox_usize(v_stop_1009_);
lean_dec(v_stop_1009_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_46541__boxed_1010_, v_as_1007_, v_i_boxed_1011_, v_stop_boxed_1012_);
lean_dec_ref(v_as_1007_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1015_, uint8_t v_t_1016_, lean_object* v_i_1017_, lean_object* v_as_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_array_get_size(v_as_1018_);
v___x_1023_ = lean_nat_dec_lt(v_i_1017_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec(v_i_1017_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_as_1018_);
return v___x_1024_;
}
else
{
lean_object* v_a_1025_; lean_object* v_type_1026_; lean_object* v___x_1027_; lean_object* v_subst_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1025_ = lean_array_fget_borrowed(v_as_1018_, v_i_1017_);
v_type_1026_ = lean_ctor_get(v_a_1025_, 2);
v___x_1027_ = lean_st_ref_get(v___y_1019_);
v_subst_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref(v_subst_1028_);
lean_dec(v___x_1027_);
lean_inc_ref(v_type_1026_);
v___x_1029_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1015_, v_subst_1028_, v_t_1016_, v_type_1026_);
lean_dec_ref(v_subst_1028_);
lean_inc(v_a_1025_);
v___x_1030_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1015_, v_a_1025_, v___x_1029_, v___y_1020_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; size_t v___x_1032_; size_t v___x_1033_; uint8_t v___x_1034_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_ptr_addr(v_a_1025_);
v___x_1033_ = lean_ptr_addr(v_a_1031_);
v___x_1034_ = lean_usize_dec_eq(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_add(v_i_1017_, v___x_1035_);
v___x_1037_ = lean_array_fset(v_as_1018_, v_i_1017_, v_a_1031_);
lean_dec(v_i_1017_);
v_i_1017_ = v___x_1036_;
v_as_1018_ = v___x_1037_;
goto _start;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v_a_1031_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_i_1017_, v___x_1039_);
lean_dec(v_i_1017_);
v_i_1017_ = v___x_1040_;
goto _start;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_as_1018_);
lean_dec(v_i_1017_);
v_a_1042_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1030_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1050_, lean_object* v_t_1051_, lean_object* v_i_1052_, lean_object* v_as_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v_pu_boxed_1057_; uint8_t v_t_boxed_1058_; lean_object* v_res_1059_; 
v_pu_boxed_1057_ = lean_unbox(v_pu_1050_);
v_t_boxed_1058_ = lean_unbox(v_t_1051_);
v_res_1059_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1057_, v_t_boxed_1058_, v_i_1052_, v_as_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1060_, uint8_t v_t_1061_, lean_object* v_ps_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1060_, v_t_1061_, v___x_1071_, v_ps_1062_, v___y_1064_, v___y_1067_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1073_, lean_object* v_t_1074_, lean_object* v_ps_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v_pu_boxed_1084_; uint8_t v_t_boxed_1085_; lean_object* v_res_1086_; 
v_pu_boxed_1084_ = lean_unbox(v_pu_1073_);
v_t_boxed_1085_ = lean_unbox(v_t_1074_);
v_res_1086_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1084_, v_t_boxed_1085_, v_ps_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1087_, uint8_t v_t_1088_, lean_object* v_decl_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_type_1093_; lean_object* v_value_1094_; lean_object* v___x_1095_; lean_object* v_subst_1096_; lean_object* v___x_1097_; lean_object* v_subst_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_type_1093_ = lean_ctor_get(v_decl_1089_, 2);
v_value_1094_ = lean_ctor_get(v_decl_1089_, 3);
v___x_1095_ = lean_st_ref_get(v___y_1090_);
v_subst_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_subst_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1090_);
v_subst_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_subst_1098_);
lean_dec(v___x_1097_);
lean_inc_ref(v_type_1093_);
v___x_1099_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1087_, v_subst_1096_, v_t_1088_, v_type_1093_);
lean_dec_ref(v_subst_1096_);
lean_inc(v_value_1094_);
v___x_1100_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1087_, v_subst_1098_, v_value_1094_, v_t_1088_);
lean_dec_ref(v_subst_1098_);
v___x_1101_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1087_, v_decl_1089_, v___x_1099_, v___x_1100_, v___y_1091_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1102_, lean_object* v_t_1103_, lean_object* v_decl_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_pu_boxed_1108_; uint8_t v_t_boxed_1109_; lean_object* v_res_1110_; 
v_pu_boxed_1108_ = lean_unbox(v_pu_1102_);
v_t_boxed_1109_ = lean_unbox(v_t_1103_);
v_res_1110_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1108_, v_t_boxed_1109_, v_decl_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1111_, lean_object* v___f_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v_fvarId_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc(v_fvarId_1115_);
v___x_1121_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1115_, v___y_1111_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref_known(v___x_1121_, 1);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1113_);
v___x_1122_ = lean_apply_9(v___f_1112_, v_fvarId_1115_, v___y_1113_, v___y_1111_, v___y_1114_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, lean_box(0));
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_fvarId_1115_);
lean_dec_ref(v___f_1112_);
v_a_1123_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1131_, lean_object* v___f_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v_fvarId_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1131_, v___f_1132_, v___y_1133_, v___y_1134_, v_fvarId_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_ks_1146_; lean_object* v_vs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1171_; 
v_ks_1146_ = lean_ctor_get(v_x_1142_, 0);
v_vs_1147_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1149_ = v_x_1142_;
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_vs_1147_);
lean_inc(v_ks_1146_);
lean_dec(v_x_1142_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_get_size(v_ks_1146_);
v___x_1152_ = lean_nat_dec_lt(v_x_1143_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec(v_x_1143_);
v___x_1153_ = lean_array_push(v_ks_1146_, v_x_1144_);
v___x_1154_ = lean_array_push(v_vs_1147_, v_x_1145_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1154_);
lean_ctor_set(v___x_1149_, 0, v___x_1153_);
v___x_1156_ = v___x_1149_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
lean_object* v_k_x27_1158_; uint8_t v___x_1159_; 
v_k_x27_1158_ = lean_array_fget_borrowed(v_ks_1146_, v_x_1143_);
v___x_1159_ = lean_name_eq(v_x_1144_, v_k_x27_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1161_; 
if (v_isShared_1150_ == 0)
{
v___x_1161_ = v___x_1149_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_ks_1146_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_vs_1147_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_x_1143_, v___x_1162_);
lean_dec(v_x_1143_);
v_x_1142_ = v___x_1161_;
v_x_1143_ = v___x_1163_;
goto _start;
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_array_fset(v_ks_1146_, v_x_1143_, v_x_1144_);
v___x_1167_ = lean_array_fset(v_vs_1147_, v_x_1143_, v_x_1145_);
lean_dec(v_x_1143_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1167_);
lean_ctor_set(v___x_1149_, 0, v___x_1166_);
v___x_1169_ = v___x_1149_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1172_, lean_object* v_k_1173_, lean_object* v_v_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1172_, v___x_1175_, v_k_1173_, v_v_1174_);
return v___x_1176_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1177_; uint64_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(1723u);
v___x_1178_ = lean_uint64_of_nat(v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1180_, size_t v_x_1181_, size_t v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_object* v_es_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v_j_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_es_1185_ = lean_ctor_get(v_x_1180_, 0);
v___x_1186_ = ((size_t)31ULL);
v___x_1187_ = lean_usize_land(v_x_1181_, v___x_1186_);
v_j_1188_ = lean_usize_to_nat(v___x_1187_);
v___x_1189_ = lean_array_get_size(v_es_1185_);
v___x_1190_ = lean_nat_dec_lt(v_j_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_dec(v_j_1188_);
lean_dec(v_x_1184_);
lean_dec(v_x_1183_);
return v_x_1180_;
}
else
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1229_; 
lean_inc_ref(v_es_1185_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_x_1180_, 0);
lean_dec(v_unused_1230_);
v___x_1192_ = v_x_1180_;
v_isShared_1193_ = v_isSharedCheck_1229_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v_x_1180_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1229_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_v_1194_; lean_object* v___x_1195_; lean_object* v_xs_x27_1196_; lean_object* v___y_1198_; 
v_v_1194_ = lean_array_fget(v_es_1185_, v_j_1188_);
v___x_1195_ = lean_box(0);
v_xs_x27_1196_ = lean_array_fset(v_es_1185_, v_j_1188_, v___x_1195_);
switch(lean_obj_tag(v_v_1194_))
{
case 0:
{
lean_object* v_key_1203_; lean_object* v_val_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1214_; 
v_key_1203_ = lean_ctor_get(v_v_1194_, 0);
v_val_1204_ = lean_ctor_get(v_v_1194_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_v_1194_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1206_ = v_v_1194_;
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_val_1204_);
lean_inc(v_key_1203_);
lean_dec(v_v_1194_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_name_eq(v_x_1183_, v_key_1203_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_del_object(v___x_1206_);
v___x_1209_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1203_, v_val_1204_, v_x_1183_, v_x_1184_);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___y_1198_ = v___x_1210_;
goto v___jp_1197_;
}
else
{
lean_object* v___x_1212_; 
lean_dec(v_val_1204_);
lean_dec(v_key_1203_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_x_1184_);
lean_ctor_set(v___x_1206_, 0, v_x_1183_);
v___x_1212_ = v___x_1206_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_x_1183_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_x_1184_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
v___y_1198_ = v___x_1212_;
goto v___jp_1197_;
}
}
}
}
case 1:
{
lean_object* v_node_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1227_; 
v_node_1215_ = lean_ctor_get(v_v_1194_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_v_1194_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1217_ = v_v_1194_;
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_node_1215_);
lean_dec(v_v_1194_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1227_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1219_ = ((size_t)5ULL);
v___x_1220_ = lean_usize_shift_right(v_x_1181_, v___x_1219_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_x_1182_, v___x_1221_);
v___x_1223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1215_, v___x_1220_, v___x_1222_, v_x_1183_, v_x_1184_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1223_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v___y_1198_ = v___x_1225_;
goto v___jp_1197_;
}
}
}
default: 
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_x_1183_);
lean_ctor_set(v___x_1228_, 1, v_x_1184_);
v___y_1198_ = v___x_1228_;
goto v___jp_1197_;
}
}
v___jp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_array_fset(v_xs_x27_1196_, v_j_1188_, v___y_1198_);
lean_dec(v_j_1188_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1199_);
v___x_1201_ = v___x_1192_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_ks_1231_; lean_object* v_vs_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1252_; 
v_ks_1231_ = lean_ctor_get(v_x_1180_, 0);
v_vs_1232_ = lean_ctor_get(v_x_1180_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1234_ = v_x_1180_;
v_isShared_1235_ = v_isSharedCheck_1252_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_vs_1232_);
lean_inc(v_ks_1231_);
lean_dec(v_x_1180_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1252_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_ks_1231_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_vs_1232_);
v___x_1237_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v_newNode_1238_; uint8_t v___y_1240_; size_t v___x_1246_; uint8_t v___x_1247_; 
v_newNode_1238_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1237_, v_x_1183_, v_x_1184_);
v___x_1246_ = ((size_t)7ULL);
v___x_1247_ = lean_usize_dec_le(v___x_1246_, v_x_1182_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1238_);
v___x_1249_ = lean_unsigned_to_nat(4u);
v___x_1250_ = lean_nat_dec_lt(v___x_1248_, v___x_1249_);
lean_dec(v___x_1248_);
v___y_1240_ = v___x_1250_;
goto v___jp_1239_;
}
else
{
v___y_1240_ = v___x_1247_;
goto v___jp_1239_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
lean_object* v_ks_1241_; lean_object* v_vs_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_ks_1241_ = lean_ctor_get(v_newNode_1238_, 0);
lean_inc_ref(v_ks_1241_);
v_vs_1242_ = lean_ctor_get(v_newNode_1238_, 1);
lean_inc_ref(v_vs_1242_);
lean_dec_ref(v_newNode_1238_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1245_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1182_, v_ks_1241_, v_vs_1242_, v___x_1243_, v___x_1244_);
lean_dec_ref(v_vs_1242_);
lean_dec_ref(v_ks_1241_);
return v___x_1245_;
}
else
{
return v_newNode_1238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1253_, lean_object* v_keys_1254_, lean_object* v_vals_1255_, lean_object* v_i_1256_, lean_object* v_entries_1257_){
_start:
{
lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = lean_array_get_size(v_keys_1254_);
v___x_1259_ = lean_nat_dec_lt(v_i_1256_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v_i_1256_);
return v_entries_1257_;
}
else
{
lean_object* v_k_1260_; lean_object* v_v_1261_; uint64_t v___y_1263_; 
v_k_1260_ = lean_array_fget_borrowed(v_keys_1254_, v_i_1256_);
v_v_1261_ = lean_array_fget_borrowed(v_vals_1255_, v_i_1256_);
if (lean_obj_tag(v_k_1260_) == 0)
{
uint64_t v___x_1274_; 
v___x_1274_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1263_ = v___x_1274_;
goto v___jp_1262_;
}
else
{
uint64_t v_hash_1275_; 
v_hash_1275_ = lean_ctor_get_uint64(v_k_1260_, sizeof(void*)*2);
v___y_1263_ = v_hash_1275_;
goto v___jp_1262_;
}
v___jp_1262_:
{
size_t v_h_1264_; size_t v___x_1265_; lean_object* v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v_h_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_h_1264_ = lean_uint64_to_usize(v___y_1263_);
v___x_1265_ = ((size_t)5ULL);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = ((size_t)1ULL);
v___x_1268_ = lean_usize_sub(v_depth_1253_, v___x_1267_);
v___x_1269_ = lean_usize_mul(v___x_1265_, v___x_1268_);
v_h_1270_ = lean_usize_shift_right(v_h_1264_, v___x_1269_);
v___x_1271_ = lean_nat_add(v_i_1256_, v___x_1266_);
lean_dec(v_i_1256_);
lean_inc(v_v_1261_);
lean_inc(v_k_1260_);
v___x_1272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1257_, v_h_1270_, v_depth_1253_, v_k_1260_, v_v_1261_);
v_i_1256_ = v___x_1271_;
v_entries_1257_ = v___x_1272_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1276_, lean_object* v_keys_1277_, lean_object* v_vals_1278_, lean_object* v_i_1279_, lean_object* v_entries_1280_){
_start:
{
size_t v_depth_boxed_1281_; lean_object* v_res_1282_; 
v_depth_boxed_1281_ = lean_unbox_usize(v_depth_1276_);
lean_dec(v_depth_1276_);
v_res_1282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1281_, v_keys_1277_, v_vals_1278_, v_i_1279_, v_entries_1280_);
lean_dec_ref(v_vals_1278_);
lean_dec_ref(v_keys_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
size_t v_x_46819__boxed_1288_; size_t v_x_46820__boxed_1289_; lean_object* v_res_1290_; 
v_x_46819__boxed_1288_ = lean_unbox_usize(v_x_1284_);
lean_dec(v_x_1284_);
v_x_46820__boxed_1289_ = lean_unbox_usize(v_x_1285_);
lean_dec(v_x_1285_);
v_res_1290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1283_, v_x_46819__boxed_1288_, v_x_46820__boxed_1289_, v_x_1286_, v_x_1287_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
uint64_t v___y_1295_; 
if (lean_obj_tag(v_x_1292_) == 0)
{
uint64_t v___x_1299_; 
v___x_1299_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1295_ = v___x_1299_;
goto v___jp_1294_;
}
else
{
uint64_t v_hash_1300_; 
v_hash_1300_ = lean_ctor_get_uint64(v_x_1292_, sizeof(void*)*2);
v___y_1295_ = v_hash_1300_;
goto v___jp_1294_;
}
v___jp_1294_:
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_uint64_to_usize(v___y_1295_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1291_, v___x_1296_, v___x_1297_, v_x_1292_, v_x_1293_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v_array_1303_; lean_object* v_start_1304_; lean_object* v_stop_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1318_; 
v_array_1303_ = lean_ctor_get(v_a_1301_, 0);
v_start_1304_ = lean_ctor_get(v_a_1301_, 1);
v_stop_1305_ = lean_ctor_get(v_a_1301_, 2);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_a_1301_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1307_ = v_a_1301_;
v_isShared_1308_ = v_isSharedCheck_1318_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_stop_1305_);
lean_inc(v_start_1304_);
lean_inc(v_array_1303_);
lean_dec(v_a_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1318_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_lt(v_start_1304_, v_stop_1305_);
if (v___x_1309_ == 0)
{
lean_del_object(v___x_1307_);
lean_dec(v_stop_1305_);
lean_dec(v_start_1304_);
lean_dec_ref(v_array_1303_);
return v_b_1302_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v_start_1304_, v___x_1310_);
lean_inc_ref(v_array_1303_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1311_);
v___x_1313_ = v___x_1307_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_array_1303_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_stop_1305_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_array_fget(v_array_1303_, v_start_1304_);
lean_dec(v_start_1304_);
lean_dec_ref(v_array_1303_);
v___x_1315_ = lean_array_push(v_b_1302_, v___x_1314_);
v_a_1301_ = v___x_1313_;
v_b_1302_ = v___x_1315_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1319_, size_t v_sz_1320_, size_t v_i_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_lt(v_i_1321_, v_sz_1320_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_b_1322_);
return v___x_1326_;
}
else
{
lean_object* v_array_1327_; lean_object* v_start_1328_; lean_object* v_stop_1329_; uint8_t v___x_1330_; 
v_array_1327_ = lean_ctor_get(v_b_1322_, 0);
v_start_1328_ = lean_ctor_get(v_b_1322_, 1);
v_stop_1329_ = lean_ctor_get(v_b_1322_, 2);
v___x_1330_ = lean_nat_dec_lt(v_start_1328_, v_stop_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1322_);
return v___x_1331_;
}
else
{
lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1364_; 
lean_inc(v_stop_1329_);
lean_inc(v_start_1328_);
lean_inc_ref(v_array_1327_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_b_1322_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1365_ = lean_ctor_get(v_b_1322_, 2);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_b_1322_, 1);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_b_1322_, 0);
lean_dec(v_unused_1367_);
v___x_1333_ = v_b_1322_;
v_isShared_1334_ = v_isSharedCheck_1364_;
goto v_resetjp_1332_;
}
else
{
lean_dec(v_b_1322_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1364_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v_fvarId_1337_; lean_object* v_subst_1338_; lean_object* v_used_1339_; lean_object* v_binderRenaming_1340_; lean_object* v_funDeclInfoMap_1341_; uint8_t v_simplified_1342_; lean_object* v_visited_1343_; lean_object* v_inline_1344_; lean_object* v_inlineLocal_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1363_; 
v___x_1335_ = lean_st_ref_take(v___y_1323_);
v_a_1336_ = lean_array_uget_borrowed(v_as_1319_, v_i_1321_);
v_fvarId_1337_ = lean_ctor_get(v_a_1336_, 0);
v_subst_1338_ = lean_ctor_get(v___x_1335_, 0);
v_used_1339_ = lean_ctor_get(v___x_1335_, 1);
v_binderRenaming_1340_ = lean_ctor_get(v___x_1335_, 2);
v_funDeclInfoMap_1341_ = lean_ctor_get(v___x_1335_, 3);
v_simplified_1342_ = lean_ctor_get_uint8(v___x_1335_, sizeof(void*)*7);
v_visited_1343_ = lean_ctor_get(v___x_1335_, 4);
v_inline_1344_ = lean_ctor_get(v___x_1335_, 5);
v_inlineLocal_1345_ = lean_ctor_get(v___x_1335_, 6);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1347_ = v___x_1335_;
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_inlineLocal_1345_);
lean_inc(v_inline_1344_);
lean_inc(v_visited_1343_);
lean_inc(v_funDeclInfoMap_1341_);
lean_inc(v_binderRenaming_1340_);
lean_inc(v_used_1339_);
lean_inc(v_subst_1338_);
lean_dec(v___x_1335_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_array_fget_borrowed(v_array_1327_, v_start_1328_);
lean_inc(v___x_1349_);
lean_inc(v_fvarId_1337_);
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1338_, v_fvarId_1337_, v___x_1349_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_used_1339_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_binderRenaming_1340_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_funDeclInfoMap_1341_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_visited_1343_);
lean_ctor_set(v_reuseFailAlloc_1362_, 5, v_inline_1344_);
lean_ctor_set(v_reuseFailAlloc_1362_, 6, v_inlineLocal_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*7, v_simplified_1342_);
v___x_1352_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1353_ = lean_st_ref_set(v___y_1323_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_start_1328_, v___x_1354_);
lean_dec(v_start_1328_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1355_);
v___x_1357_ = v___x_1333_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_array_1327_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_stop_1329_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
size_t v___x_1358_; size_t v___x_1359_; 
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_add(v_i_1321_, v___x_1358_);
v_i_1321_ = v___x_1359_;
v_b_1322_ = v___x_1357_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1368_, lean_object* v_sz_1369_, lean_object* v_i_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
size_t v_sz_boxed_1374_; size_t v_i_boxed_1375_; lean_object* v_res_1376_; 
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1369_);
lean_dec(v_sz_1369_);
v_i_boxed_1375_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1368_, v_sz_boxed_1374_, v_i_boxed_1375_, v_b_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v_as_1368_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1377_, size_t v_i_1378_, size_t v_stop_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_usize_dec_eq(v_i_1378_, v_stop_1379_);
if (v___x_1383_ == 0)
{
uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = 0;
v___x_1385_ = lean_array_uget_borrowed(v_as_1377_, v_i_1378_);
v___x_1386_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1384_, v___x_1385_, v___y_1381_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; size_t v___x_1388_; size_t v___x_1389_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1378_, v___x_1388_);
v_i_1378_ = v___x_1389_;
v_b_1380_ = v_a_1387_;
goto _start;
}
else
{
return v___x_1386_;
}
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_b_1380_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1392_, lean_object* v_i_1393_, lean_object* v_stop_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
size_t v_i_boxed_1398_; size_t v_stop_boxed_1399_; lean_object* v_res_1400_; 
v_i_boxed_1398_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_stop_boxed_1399_ = lean_unbox_usize(v_stop_1394_);
lean_dec(v_stop_1394_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1392_, v_i_boxed_1398_, v_stop_boxed_1399_, v_b_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v_as_1392_);
return v_res_1400_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = 0;
v___x_1402_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1405_ = lean_panic_fn_borrowed(v___x_1404_, v_msg_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1406_, size_t v_i_1407_, size_t v_stop_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_eq(v_i_1407_, v_stop_1408_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v_type_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_array_uget_borrowed(v_as_1406_, v_i_1407_);
v_type_1413_ = lean_ctor_get(v___x_1412_, 2);
v___x_1414_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1413_, v___y_1409_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1426_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_unbox(v_a_1415_);
if (v___x_1419_ == 0)
{
size_t v___x_1420_; size_t v___x_1421_; 
lean_del_object(v___x_1417_);
lean_dec(v_a_1415_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1407_, v___x_1420_);
v_i_1407_ = v___x_1421_;
goto _start;
}
else
{
lean_object* v___x_1424_; 
if (v_isShared_1418_ == 0)
{
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1415_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
return v___x_1414_;
}
}
else
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = 0;
v___x_1428_ = lean_box(v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1430_, lean_object* v_i_1431_, lean_object* v_stop_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
size_t v_i_boxed_1435_; size_t v_stop_boxed_1436_; lean_object* v_res_1437_; 
v_i_boxed_1435_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_stop_boxed_1436_ = lean_unbox_usize(v_stop_1432_);
lean_dec(v_stop_1432_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1430_, v_i_boxed_1435_, v_stop_boxed_1436_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v_as_1430_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1438_, size_t v_i_1439_, size_t v_stop_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_eq(v_i_1439_, v_stop_1440_);
if (v___x_1444_ == 0)
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = 0;
v___x_1446_ = lean_array_uget_borrowed(v_as_1438_, v_i_1439_);
v___x_1447_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1445_, v___x_1446_, v___y_1442_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; size_t v___x_1449_; size_t v___x_1450_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = lean_usize_add(v_i_1439_, v___x_1449_);
v_i_1439_ = v___x_1450_;
v_b_1441_ = v_a_1448_;
goto _start;
}
else
{
return v___x_1447_;
}
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_b_1441_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1453_, lean_object* v_i_1454_, lean_object* v_stop_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_i_boxed_1459_; size_t v_stop_boxed_1460_; lean_object* v_res_1461_; 
v_i_boxed_1459_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_stop_boxed_1460_ = lean_unbox_usize(v_stop_1455_);
lean_dec(v_stop_1455_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1453_, v_i_boxed_1459_, v_stop_boxed_1460_, v_b_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v_as_1453_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1462_, size_t v_i_1463_, size_t v_stop_1464_, lean_object* v_b_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_a_1472_; lean_object* v___y_1477_; uint8_t v___x_1479_; 
v___x_1479_ = lean_usize_dec_eq(v_i_1463_, v_stop_1464_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_array_uget_borrowed(v_as_1462_, v_i_1463_);
v___x_1482_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1481_);
v___x_1483_ = lean_array_get_size(v___x_1482_);
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_nat_dec_lt(v___x_1480_, v___x_1483_);
if (v___x_1485_ == 0)
{
lean_dec_ref(v___x_1482_);
v_a_1472_ = v___x_1484_;
goto v___jp_1471_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_le(v___x_1483_, v___x_1483_);
if (v___x_1486_ == 0)
{
if (v___x_1485_ == 0)
{
lean_dec_ref(v___x_1482_);
v_a_1472_ = v___x_1484_;
goto v___jp_1471_;
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1483_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1482_, v___x_1487_, v___x_1488_, v___x_1484_, v___y_1467_);
lean_dec_ref(v___x_1482_);
v___y_1477_ = v___x_1489_;
goto v___jp_1476_;
}
}
else
{
size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = lean_usize_of_nat(v___x_1483_);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1482_, v___x_1490_, v___x_1491_, v___x_1484_, v___y_1467_);
lean_dec_ref(v___x_1482_);
v___y_1477_ = v___x_1492_;
goto v___jp_1476_;
}
}
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_b_1465_);
return v___x_1493_;
}
v___jp_1471_:
{
size_t v___x_1473_; size_t v___x_1474_; 
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_add(v_i_1463_, v___x_1473_);
v_i_1463_ = v___x_1474_;
v_b_1465_ = v_a_1472_;
goto _start;
}
v___jp_1476_:
{
if (lean_obj_tag(v___y_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___y_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___y_1477_, 1);
v_a_1472_ = v_a_1478_;
goto v___jp_1471_;
}
else
{
return v___y_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1494_, lean_object* v_i_1495_, lean_object* v_stop_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
size_t v_i_boxed_1503_; size_t v_stop_boxed_1504_; lean_object* v_res_1505_; 
v_i_boxed_1503_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_stop_boxed_1504_ = lean_unbox_usize(v_stop_1496_);
lean_dec(v_stop_1496_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1494_, v_i_boxed_1503_, v_stop_boxed_1504_, v_b_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_as_1494_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1506_, size_t v_i_1507_, size_t v_stop_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_usize_dec_eq(v_i_1507_, v_stop_1508_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v_fvarId_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_array_uget_borrowed(v_as_1506_, v_i_1507_);
v_fvarId_1513_ = lean_ctor_get(v___x_1512_, 0);
v___x_1514_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1513_, v___y_1509_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1526_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_unbox(v_a_1515_);
if (v___x_1519_ == 0)
{
size_t v___x_1520_; size_t v___x_1521_; 
lean_del_object(v___x_1517_);
lean_dec(v_a_1515_);
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_add(v_i_1507_, v___x_1520_);
v_i_1507_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v___x_1524_; 
if (v_isShared_1518_ == 0)
{
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1515_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
return v___x_1514_;
}
}
else
{
uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = 0;
v___x_1528_ = lean_box(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1530_, lean_object* v_i_1531_, lean_object* v_stop_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
size_t v_i_boxed_1535_; size_t v_stop_boxed_1536_; lean_object* v_res_1537_; 
v_i_boxed_1535_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_stop_boxed_1536_ = lean_unbox_usize(v_stop_1532_);
lean_dec(v_stop_1532_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1530_, v_i_boxed_1535_, v_stop_boxed_1536_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v_as_1530_);
return v_res_1537_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1541_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1542_ = lean_unsigned_to_nat(9u);
v___x_1543_ = lean_unsigned_to_nat(641u);
v___x_1544_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1545_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1546_ = l_mkPanicMessageWithDecl(v___x_1545_, v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v_fvarId_1552_, lean_object* v_k_1553_, lean_object* v_args_1554_, uint8_t v___x_1555_, lean_object* v___x_1556_, lean_object* v_result_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_lower_1567_; lean_object* v_upper_1568_; uint8_t v___x_1595_; 
v___x_1595_ = lean_nat_dec_lt(v___x_1550_, v___x_1551_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v___x_1556_);
lean_dec_ref(v_args_1554_);
lean_dec(v___x_1551_);
lean_dec(v___x_1550_);
v___x_1596_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1552_, v_result_1557_, v___y_1559_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1596_, 1);
lean_inc_ref(v___y_1563_);
v___x_1597_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1553_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1597_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref(v_k_1553_);
v_a_1598_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1596_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_nat_dec_le(v___x_1550_, v___x_1556_);
if (v___x_1606_ == 0)
{
lean_dec(v___x_1556_);
v_lower_1567_ = v___x_1550_;
v_upper_1568_ = v___x_1551_;
goto v___jp_1566_;
}
else
{
lean_dec(v___x_1550_);
v_lower_1567_ = v___x_1556_;
v_upper_1568_ = v___x_1551_;
goto v___jp_1566_;
}
}
v___jp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1569_ = l_Array_toSubarray___redArg(v_args_1554_, v_lower_1567_, v_upper_1568_);
v___x_1570_ = l_Subarray_copy___redArg(v___x_1569_);
v___x_1571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_result_1557_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1573_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1555_, v___x_1571_, v___x_1572_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_fvarId_1575_; lean_object* v___x_1576_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_fvarId_1575_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_fvarId_1575_);
v___x_1576_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1552_, v_fvarId_1575_, v___y_1559_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1574_);
lean_ctor_set(v___x_1577_, 1, v_k_1553_);
lean_inc_ref(v___y_1563_);
v___x_1578_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1577_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1574_);
lean_dec_ref(v_k_1553_);
v_a_1579_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1576_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1576_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_k_1553_);
lean_dec(v_fvarId_1552_);
v_a_1587_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1573_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1573_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v_fvarId_1609_, lean_object* v_k_1610_, lean_object* v_args_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, lean_object* v_result_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v___x_47344__boxed_1623_; lean_object* v_res_1624_; 
v___x_47344__boxed_1623_ = lean_unbox(v___x_1612_);
v_res_1624_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1607_, v___x_1608_, v_fvarId_1609_, v_k_1610_, v_args_1611_, v___x_47344__boxed_1623_, v___x_1613_, v_result_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1625_, lean_object* v_k_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_fvarId_1635_; lean_object* v_value_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1974_; 
v_fvarId_1635_ = lean_ctor_get(v_letDecl_1625_, 0);
v_value_1636_ = lean_ctor_get(v_letDecl_1625_, 3);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_letDecl_1625_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1975_ = lean_ctor_get(v_letDecl_1625_, 2);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_letDecl_1625_, 1);
lean_dec(v_unused_1976_);
v___x_1638_ = v_letDecl_1625_;
v_isShared_1639_ = v_isSharedCheck_1974_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_value_1636_);
lean_inc(v_fvarId_1635_);
lean_dec(v_letDecl_1625_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1974_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; 
lean_inc(v_value_1636_);
v___x_1640_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1636_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1965_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1965_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1965_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
if (lean_obj_tag(v_a_1641_) == 1)
{
lean_object* v_val_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1643_);
v_val_1645_ = lean_ctor_get(v_a_1641_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_a_1641_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1647_ = v_a_1641_;
v_isShared_1648_ = v_isSharedCheck_1960_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_val_1645_);
lean_dec(v_a_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1960_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v_params_1649_; lean_object* v_value_1650_; lean_object* v_fType_1651_; lean_object* v_args_1652_; uint8_t v_recursive_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; uint8_t v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; 
v_params_1649_ = lean_ctor_get(v_val_1645_, 0);
v_value_1650_ = lean_ctor_get(v_val_1645_, 1);
v_fType_1651_ = lean_ctor_get(v_val_1645_, 2);
v_args_1652_ = lean_ctor_get(v_val_1645_, 3);
v_recursive_1653_ = lean_ctor_get_uint8(v_val_1645_, sizeof(void*)*4 + 2);
v___x_1654_ = lean_array_get_size(v_args_1652_);
v___x_1655_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1645_);
v___x_1656_ = lean_nat_dec_lt(v___x_1654_, v___x_1655_);
if (lean_obj_tag(v_value_1636_) == 3)
{
lean_object* v_declName_1940_; lean_object* v___x_1941_; 
v_declName_1940_ = lean_ctor_get(v_value_1636_, 0);
lean_inc_n(v_declName_1940_, 2);
lean_dec_ref_known(v_value_1636_, 3);
v___x_1941_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1653_, v_declName_1940_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_declName_1943_; lean_object* v_config_1944_; lean_object* v_inlineStack_1945_; lean_object* v_inlineStackOccs_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_declName_1943_ = lean_ctor_get(v_a_1627_, 0);
v_config_1944_ = lean_ctor_get(v_a_1627_, 1);
v_inlineStack_1945_ = lean_ctor_get(v_a_1627_, 2);
v_inlineStackOccs_1946_ = lean_ctor_get(v_a_1627_, 3);
lean_inc(v_inlineStack_1945_);
lean_inc(v_declName_1940_);
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_declName_1940_);
lean_ctor_set(v___x_1947_, 1, v_inlineStack_1945_);
lean_inc_ref(v_inlineStackOccs_1946_);
v___x_1948_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1946_, v_declName_1940_, v_a_1942_);
lean_inc_ref(v_config_1944_);
lean_inc(v_declName_1943_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 3, v___x_1948_);
lean_ctor_set(v___x_1638_, 2, v___x_1947_);
lean_ctor_set(v___x_1638_, 1, v_config_1944_);
lean_ctor_set(v___x_1638_, 0, v_declName_1943_);
v___x_1950_ = v___x_1638_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_declName_1943_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_config_1944_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
v___y_1839_ = v___x_1950_;
v___y_1840_ = v_a_1628_;
v___y_1841_ = v_a_1629_;
v___y_1842_ = v_a_1630_;
v___y_1843_ = v_a_1631_;
v___y_1844_ = v_a_1632_;
v___y_1845_ = v_a_1633_;
goto v___jp_1838_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_declName_1940_);
lean_dec(v___x_1655_);
lean_del_object(v___x_1647_);
lean_dec(v_val_1645_);
lean_del_object(v___x_1638_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
v_a_1952_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1941_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1941_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_del_object(v___x_1638_);
lean_dec(v_value_1636_);
lean_inc_ref(v_a_1627_);
v___y_1839_ = v_a_1627_;
v___y_1840_ = v_a_1628_;
v___y_1841_ = v_a_1629_;
v___y_1842_ = v_a_1630_;
v___y_1843_ = v_a_1631_;
v___y_1844_ = v_a_1632_;
v___y_1845_ = v_a_1633_;
goto v___jp_1838_;
}
v___jp_1657_:
{
lean_object* v___x_1671_; 
lean_inc_ref(v___y_1665_);
v___x_1671_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1670_, v___y_1661_, v___y_1663_, v___y_1659_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1663_);
if (lean_obj_tag(v___x_1673_) == 0)
{
uint8_t v___x_1674_; 
lean_dec_ref_known(v___x_1673_, 1);
v___x_1674_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1672_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v___y_1664_);
v___x_1675_ = lean_mk_empty_array_with_capacity(v___y_1660_);
lean_dec(v___y_1660_);
lean_inc_ref(v___x_1675_);
v___x_1676_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1662_, v___x_1675_);
v___x_1677_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1668_, v_fType_1651_, v___x_1676_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc_n(v_a_1678_, 2);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = l_Lean_Expr_headBeta(v_a_1678_);
v___x_1680_ = l_Lean_Expr_isForall(v___x_1679_);
lean_dec_ref(v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref(v___x_1675_);
v___x_1681_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1668_, v_a_1678_, v___x_1656_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_fvarId_1683_; lean_object* v___x_1684_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v_fvarId_1683_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1667_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1663_);
lean_inc(v_fvarId_1683_);
v___x_1684_ = lean_apply_9(v___y_1669_, v_fvarId_1683_, v___y_1661_, v___y_1663_, v___y_1659_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_, lean_box(0));
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
v___x_1688_ = lean_array_push(v___x_1687_, v_a_1682_);
v___x_1689_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1690_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1668_, v___x_1688_, v_a_1685_, v___x_1689_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc_n(v_a_1691_, 2);
lean_dec_ref_known(v___x_1690_, 1);
v___f_1692_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1692_, 0, v_a_1691_);
lean_closure_set(v___f_1692_, 1, v___x_1686_);
v___x_1693_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1668_, v_a_1672_, v___f_1692_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1705_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_a_1691_);
lean_ctor_set(v___x_1698_, 1, v_a_1694_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1698_);
v___x_1700_ = v___x_1647_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1700_);
v___x_1702_ = v___x_1696_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_a_1691_);
lean_del_object(v___x_1647_);
v_a_1706_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1693_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1693_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_a_1672_);
lean_del_object(v___x_1647_);
v_a_1714_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1690_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1690_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1682_);
lean_dec(v_a_1672_);
lean_del_object(v___x_1647_);
v_a_1722_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1684_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1684_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
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
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1672_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1661_);
lean_del_object(v___x_1647_);
v_a_1730_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1681_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1681_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_a_1678_);
v___x_1738_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1739_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1675_, v_a_1672_, v___x_1738_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1740_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v_fvarId_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v_fvarId_1743_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1667_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1661_);
lean_inc(v_fvarId_1743_);
v___x_1744_ = lean_apply_9(v___y_1669_, v_fvarId_1743_, v___y_1661_, v___y_1663_, v___y_1659_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_, lean_box(0));
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_a_1742_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1747_);
v___x_1749_ = lean_array_push(v___x_1748_, v___x_1746_);
v___x_1750_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1749_, v_a_1745_, v___y_1661_, v___y_1663_, v___y_1659_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v___x_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1761_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v_a_1751_);
v___x_1756_ = v___x_1647_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1647_);
v_a_1762_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1750_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1750_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1742_);
lean_dec_ref(v___y_1661_);
lean_del_object(v___x_1647_);
v_a_1770_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1744_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1744_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1661_);
lean_del_object(v___x_1647_);
v_a_1778_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1741_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1741_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1661_);
lean_del_object(v___x_1647_);
v_a_1786_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1739_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1739_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___x_1675_);
lean_dec(v_a_1672_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1661_);
lean_del_object(v___x_1647_);
v_a_1794_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1677_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1677_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
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
lean_object* v___x_1802_; 
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v_fType_1651_);
v___x_1802_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1668_, v_a_1672_, v___y_1664_, v___y_1667_, v___y_1666_, v___y_1665_, v___y_1658_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v_a_1803_);
v___x_1808_ = v___x_1647_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_del_object(v___x_1647_);
v_a_1814_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1802_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1672_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v_fType_1651_);
lean_del_object(v___x_1647_);
v_a_1822_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1673_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1673_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v___y_1669_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v_fType_1651_);
lean_del_object(v___x_1647_);
v_a_1830_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1671_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1671_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
v___jp_1838_:
{
if (v___x_1656_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_inc_ref_n(v_args_1652_, 2);
lean_inc_ref(v_fType_1651_);
lean_inc_ref(v_value_1650_);
lean_inc_ref(v_params_1649_);
lean_dec(v_val_1645_);
v___x_1846_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1655_);
v___x_1847_ = l_Array_toSubarray___redArg(v_args_1652_, v___x_1846_, v___x_1655_);
lean_inc_ref(v___x_1847_);
v___x_1848_ = l_Subarray_copy___redArg(v___x_1847_);
v___x_1849_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1649_, v_value_1650_, v___x_1848_, v___x_1656_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v_params_1649_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; uint8_t v___x_1855_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = 0;
v___x_1852_ = lean_box(v___x_1851_);
lean_inc_ref(v_k_1626_);
lean_inc(v_fvarId_1635_);
lean_inc(v___x_1655_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1853_, 0, v___x_1655_);
lean_closure_set(v___f_1853_, 1, v___x_1654_);
lean_closure_set(v___f_1853_, 2, v_fvarId_1635_);
lean_closure_set(v___f_1853_, 3, v_k_1626_);
lean_closure_set(v___f_1853_, 4, v_args_1652_);
lean_closure_set(v___f_1853_, 5, v___x_1852_);
lean_closure_set(v___f_1853_, 6, v___x_1846_);
lean_inc_ref(v___y_1841_);
lean_inc_ref(v___y_1839_);
lean_inc_ref(v___f_1853_);
lean_inc(v___y_1840_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1854_, 0, v___y_1840_);
lean_closure_set(v___f_1854_, 1, v___f_1853_);
lean_closure_set(v___f_1854_, 2, v___y_1839_);
lean_closure_set(v___f_1854_, 3, v___y_1841_);
v___x_1855_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1626_, v_fvarId_1635_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
if (v___x_1855_ == 0)
{
lean_dec(v___x_1655_);
v___y_1658_ = v___y_1845_;
v___y_1659_ = v___y_1841_;
v___y_1660_ = v___x_1846_;
v___y_1661_ = v___y_1839_;
v___y_1662_ = v___x_1847_;
v___y_1663_ = v___y_1840_;
v___y_1664_ = v___f_1854_;
v___y_1665_ = v___y_1844_;
v___y_1666_ = v___y_1843_;
v___y_1667_ = v___y_1842_;
v___y_1668_ = v___x_1851_;
v___y_1669_ = v___f_1853_;
v___y_1670_ = v_a_1850_;
goto v___jp_1657_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_eq(v___x_1654_, v___x_1655_);
lean_dec(v___x_1655_);
if (v___x_1856_ == 0)
{
v___y_1658_ = v___y_1845_;
v___y_1659_ = v___y_1841_;
v___y_1660_ = v___x_1846_;
v___y_1661_ = v___y_1839_;
v___y_1662_ = v___x_1847_;
v___y_1663_ = v___y_1840_;
v___y_1664_ = v___f_1854_;
v___y_1665_ = v___y_1844_;
v___y_1666_ = v___y_1843_;
v___y_1667_ = v___y_1842_;
v___y_1668_ = v___x_1851_;
v___y_1669_ = v___f_1853_;
v___y_1670_ = v_a_1850_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v___f_1854_);
lean_dec_ref(v___f_1853_);
lean_dec_ref(v___x_1847_);
lean_dec_ref(v_fType_1651_);
lean_del_object(v___x_1647_);
v___x_1857_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1840_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref_known(v___x_1857_, 1);
lean_inc_ref(v___y_1844_);
v___x_1858_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1850_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v___y_1839_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1858_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_a_1850_);
lean_dec_ref(v___y_1839_);
v_a_1876_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1857_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1857_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___x_1847_);
lean_dec_ref(v___y_1839_);
lean_dec(v___x_1655_);
lean_dec_ref(v_args_1652_);
lean_dec_ref(v_fType_1651_);
lean_del_object(v___x_1647_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
v_a_1884_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1849_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1849_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v___x_1655_);
lean_del_object(v___x_1647_);
v___x_1892_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1645_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v_fvarId_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v_fvarId_1894_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_fvarId_1894_);
v___x_1895_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1635_, v_fvarId_1894_, v___y_1840_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1896_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1840_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec_ref_known(v___x_1896_, 1);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1893_);
lean_ctor_set(v___x_1897_, 1, v_k_1626_);
lean_inc_ref(v___y_1844_);
v___x_1898_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1897_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v___y_1839_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
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
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1898_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1898_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1893_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_k_1626_);
v_a_1916_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1896_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1896_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_a_1893_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_k_1626_);
v_a_1924_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1895_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1895_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___y_1839_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
v_a_1932_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1892_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1892_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_dec(v_a_1641_);
lean_del_object(v___x_1638_);
lean_dec(v_value_1636_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
v___x_1961_ = lean_box(0);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1961_);
v___x_1963_ = v___x_1643_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_del_object(v___x_1638_);
lean_dec(v_value_1636_);
lean_dec(v_fvarId_1635_);
lean_dec_ref(v_k_1626_);
v_a_1966_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1640_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1640_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = 0;
v___x_1978_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_typeName_1991_; lean_object* v_discr_1992_; lean_object* v___x_1993_; lean_object* v_subst_1994_; uint8_t v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; 
v_typeName_1991_ = lean_ctor_get(v_cases_1979_, 0);
v_discr_1992_ = lean_ctor_get(v_cases_1979_, 2);
v___x_1993_ = lean_st_ref_get(v_a_1981_);
v_subst_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_ref(v_subst_1994_);
lean_dec(v___x_1993_);
v___x_1995_ = 0;
v___x_1996_ = 0;
lean_inc(v_discr_1992_);
v___x_1997_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1994_, v_discr_1992_, v___x_1996_);
lean_dec_ref(v_subst_1994_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_fvarId_1998_; lean_object* v___x_1999_; 
v_fvarId_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_fvarId_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1998_, v_a_1982_, v_a_1984_, v_a_1986_);
lean_dec(v_fvarId_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2229_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2229_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2229_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_a_2000_) == 1)
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2224_; 
v_val_2004_ = lean_ctor_get(v_a_2000_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2006_ = v_a_2000_;
v_isShared_2007_ = v_isSharedCheck_2224_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v_a_2000_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2224_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v_env_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_st_ref_get(v_a_1986_);
v_env_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_env_2009_);
lean_dec(v___x_2008_);
v___x_2010_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_2004_);
lean_inc(v___x_2010_);
v___x_2011_ = l_Lean_Environment_find_x3f(v_env_2009_, v___x_2010_, v___x_1996_);
if (lean_obj_tag(v___x_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2223_; 
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2223_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2223_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
if (lean_obj_tag(v_val_2012_) == 6)
{
lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2222_; 
v_val_2016_ = lean_ctor_get(v_val_2012_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_val_2012_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2018_ = v_val_2012_;
v_isShared_2019_ = v_isSharedCheck_2222_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v_val_2012_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2222_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_induct_2020_; uint8_t v___x_2021_; 
v_induct_2020_ = lean_ctor_get(v_val_2016_, 1);
lean_inc(v_induct_2020_);
lean_dec_ref(v_val_2016_);
v___x_2021_ = lean_name_eq(v_typeName_1991_, v_induct_2020_);
lean_dec(v_induct_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2014_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
lean_dec_ref(v_cases_1979_);
v___x_2022_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2022_);
v___x_2024_ = v___x_2002_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
else
{
lean_object* v___x_2026_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2221_; 
lean_del_object(v___x_2002_);
v___x_2026_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1995_, v_cases_1979_, v___x_2010_);
v_fst_2027_ = lean_ctor_get(v___x_2026_, 0);
v_snd_2028_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2221_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snd_2028_);
lean_inc(v_fst_2027_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2221_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 4);
lean_ctor_set(v___x_2018_, 0, v_snd_2028_);
v___x_2033_ = v___x_2018_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_snd_2028_);
v___x_2033_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1995_, v___x_2033_, v_a_1984_);
lean_dec_ref(v___x_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2034_, 1);
v___x_2035_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1981_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref_known(v___x_2035_, 1);
if (lean_obj_tag(v_fst_2027_) == 0)
{
if (lean_obj_tag(v_val_2004_) == 0)
{
lean_object* v_params_2036_; lean_object* v_code_2037_; lean_object* v_val_2038_; lean_object* v_args_2039_; lean_object* v_lower_2041_; lean_object* v_upper_2042_; lean_object* v_numParams_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
lean_del_object(v___x_2030_);
lean_del_object(v___x_2006_);
v_params_2036_ = lean_ctor_get(v_fst_2027_, 1);
lean_inc_ref(v_params_2036_);
v_code_2037_ = lean_ctor_get(v_fst_2027_, 2);
lean_inc_ref(v_code_2037_);
lean_dec_ref_known(v_fst_2027_, 3);
v_val_2038_ = lean_ctor_get(v_val_2004_, 0);
lean_inc_ref(v_val_2038_);
v_args_2039_ = lean_ctor_get(v_val_2004_, 1);
lean_inc_ref(v_args_2039_);
lean_dec_ref_known(v_val_2004_, 2);
v_numParams_2085_ = lean_ctor_get(v_val_2038_, 3);
lean_inc(v_numParams_2085_);
lean_dec_ref(v_val_2038_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_array_get_size(v_args_2039_);
v___x_2088_ = lean_nat_dec_le(v_numParams_2085_, v___x_2086_);
if (v___x_2088_ == 0)
{
v_lower_2041_ = v_numParams_2085_;
v_upper_2042_ = v___x_2087_;
goto v___jp_2040_;
}
else
{
lean_dec(v_numParams_2085_);
v_lower_2041_ = v___x_2086_;
v_upper_2042_ = v___x_2087_;
goto v___jp_2040_;
}
v___jp_2040_:
{
lean_object* v___x_2043_; size_t v_sz_2044_; size_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2043_ = l_Array_toSubarray___redArg(v_args_2039_, v_lower_2041_, v_upper_2042_);
v_sz_2044_ = lean_array_size(v_params_2036_);
v___x_2045_ = ((size_t)0ULL);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2036_, v_sz_2044_, v___x_2045_, v___x_2043_, v_a_1981_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref_known(v___x_2046_, 1);
lean_inc_ref(v_a_1985_);
v___x_2047_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2037_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1995_, v_params_2036_, v_a_1984_);
lean_dec_ref(v_params_2036_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2049_, 0);
lean_dec(v_unused_2060_);
v___x_2051_ = v___x_2049_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v___x_2049_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_a_2048_);
v___x_2054_ = v___x_2014_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2048_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_2048_);
lean_del_object(v___x_2014_);
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2049_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2049_);
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
lean_dec_ref(v_params_2036_);
lean_del_object(v___x_2014_);
v_a_2069_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2047_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2047_);
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
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_code_2037_);
lean_dec_ref(v_params_2036_);
lean_del_object(v___x_2014_);
v_a_2077_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2046_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2046_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_params_2089_; lean_object* v_code_2090_; lean_object* v_n_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2182_; 
v_params_2089_ = lean_ctor_get(v_fst_2027_, 1);
lean_inc_ref(v_params_2089_);
v_code_2090_ = lean_ctor_get(v_fst_2027_, 2);
lean_inc_ref(v_code_2090_);
lean_dec_ref_known(v_fst_2027_, 3);
v_n_2091_ = lean_ctor_get(v_val_2004_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_val_2004_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2093_ = v_val_2004_;
v_isShared_2094_ = v_isSharedCheck_2182_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_n_2091_);
lean_dec(v_val_2004_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2182_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_zero_2095_; uint8_t v_isZero_2096_; 
v_zero_2095_ = lean_unsigned_to_nat(0u);
v_isZero_2096_ = lean_nat_dec_eq(v_n_2091_, v_zero_2095_);
if (v_isZero_2096_ == 1)
{
lean_object* v___x_2097_; 
lean_del_object(v___x_2093_);
lean_dec(v_n_2091_);
lean_dec_ref(v_params_2089_);
lean_del_object(v___x_2030_);
lean_del_object(v___x_2006_);
lean_inc_ref(v_a_1985_);
v___x_2097_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2090_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2108_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_a_2098_);
v___x_2103_ = v___x_2014_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2103_);
v___x_2105_ = v___x_2100_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_del_object(v___x_2014_);
v_a_2109_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2097_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2097_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_one_2117_; lean_object* v_n_2118_; lean_object* v___x_2120_; 
v_one_2117_ = lean_unsigned_to_nat(1u);
v_n_2118_ = lean_nat_sub(v_n_2091_, v_one_2117_);
lean_dec(v_n_2091_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 0);
lean_ctor_set(v___x_2093_, 0, v_n_2118_);
v___x_2120_ = v___x_2093_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_n_2118_);
v___x_2120_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2120_);
v___x_2122_ = v___x_2006_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2124_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1995_, v___x_2122_, v___x_2123_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_fvarId_2128_; lean_object* v_fvarId_2129_; lean_object* v___x_2130_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2127_ = lean_array_get_borrowed(v___x_2126_, v_params_2089_, v_zero_2095_);
v_fvarId_2128_ = lean_ctor_get(v___x_2127_, 0);
v_fvarId_2129_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_fvarId_2129_);
lean_inc(v_fvarId_2128_);
v___x_2130_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2128_, v_fvarId_2129_, v_a_1981_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
lean_dec_ref_known(v___x_2130_, 1);
lean_inc_ref(v_a_1985_);
v___x_2131_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2090_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1995_, v_params_2089_, v_a_1984_);
lean_dec_ref(v_params_2089_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2147_);
v___x_2135_ = v___x_2133_;
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v___x_2133_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v_a_2132_);
lean_ctor_set(v___x_2030_, 0, v_a_2125_);
v___x_2138_ = v___x_2030_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2125_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_a_2132_);
v___x_2138_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2138_);
v___x_2140_ = v___x_2014_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2140_);
v___x_2142_ = v___x_2135_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2132_);
lean_dec(v_a_2125_);
lean_del_object(v___x_2030_);
lean_del_object(v___x_2014_);
v_a_2148_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2133_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2133_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2125_);
lean_dec_ref(v_params_2089_);
lean_del_object(v___x_2030_);
lean_del_object(v___x_2014_);
v_a_2156_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2131_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2131_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2125_);
lean_dec_ref(v_code_2090_);
lean_dec_ref(v_params_2089_);
lean_del_object(v___x_2030_);
lean_del_object(v___x_2014_);
v_a_2164_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2130_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2130_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_code_2090_);
lean_dec_ref(v_params_2089_);
lean_del_object(v___x_2030_);
lean_del_object(v___x_2014_);
v_a_2172_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2124_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2124_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
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
lean_object* v_code_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2030_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
v_code_2183_ = lean_ctor_get(v_fst_2027_, 0);
lean_inc_ref(v_code_2183_);
lean_dec_ref_known(v_fst_2027_, 1);
lean_inc_ref(v_a_1985_);
v___x_2184_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2183_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2195_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_a_2185_);
v___x_2190_ = v___x_2014_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
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
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_del_object(v___x_2014_);
v_a_2196_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2184_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2184_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_del_object(v___x_2030_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2014_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
v_a_2204_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2035_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2035_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2030_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2014_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
v_a_2212_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2034_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2034_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
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
lean_del_object(v___x_2014_);
lean_dec(v_val_2012_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
lean_del_object(v___x_2002_);
lean_dec_ref(v_cases_1979_);
goto v___jp_1988_;
}
}
}
else
{
lean_dec(v___x_2011_);
lean_dec(v___x_2010_);
lean_del_object(v___x_2006_);
lean_dec(v_val_2004_);
lean_del_object(v___x_2002_);
lean_dec_ref(v_cases_1979_);
goto v___jp_1988_;
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_dec(v_a_2000_);
lean_dec_ref(v_cases_1979_);
v___x_2225_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2225_);
v___x_2227_ = v___x_2002_;
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
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_cases_1979_);
v_a_2230_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_1999_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_1999_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v___x_2238_; 
lean_dec_ref(v_cases_1979_);
v___x_2238_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1995_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2247_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_a_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2243_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2238_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2238_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2256_, uint8_t v___y_2257_, lean_object* v_i_2258_, lean_object* v_as_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_array_get_size(v_as_2259_);
v___x_2269_ = lean_nat_dec_lt(v_i_2258_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_as_2259_);
return v___x_2270_;
}
else
{
lean_object* v_a_2271_; lean_object* v_a_2273_; 
v_a_2271_ = lean_array_fget_borrowed(v_as_2259_, v_i_2258_);
if (lean_obj_tag(v_a_2271_) == 0)
{
lean_object* v_ctorName_2284_; lean_object* v_params_2285_; lean_object* v_code_2286_; uint8_t v___x_2309_; uint8_t v___y_2311_; uint8_t v___y_2312_; uint8_t v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_ctorName_2284_ = lean_ctor_get(v_a_2271_, 0);
v_params_2285_ = lean_ctor_get(v_a_2271_, 1);
v_code_2286_ = lean_ctor_get(v_a_2271_, 2);
v___x_2309_ = 0;
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v_params_2285_);
v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
v_a_2345_ = v___x_2348_;
goto v___jp_2344_;
}
else
{
if (v___x_2348_ == 0)
{
v_a_2345_ = v___x_2348_;
goto v___jp_2344_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2347_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2285_, v___x_2349_, v___x_2350_, v___y_2266_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; uint8_t v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = lean_unbox(v_a_2352_);
lean_dec(v_a_2352_);
v_a_2345_ = v___x_2353_;
goto v___jp_2344_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2354_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2351_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2351_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
v___jp_2287_:
{
lean_object* v___x_2288_; 
lean_inc_ref(v_params_2285_);
lean_inc(v_ctorName_2284_);
lean_inc(v_fvarId_2256_);
v___x_2288_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2256_, v_ctorName_2284_, v_params_2285_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
lean_inc_ref(v___y_2265_);
lean_inc_ref(v_code_2286_);
v___x_2290_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2286_, v___y_2260_, v___y_2261_, v_a_2289_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v_a_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
lean_inc_ref(v_a_2271_);
v___x_2292_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2271_, v_a_2291_);
v_a_2273_ = v___x_2292_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2293_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2290_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2290_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2301_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2288_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2288_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
v___jp_2310_:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_bool_not(v___y_2312_);
if (v___x_2313_ == 0)
{
goto v___jp_2287_;
}
else
{
if (v___y_2311_ == 0)
{
goto v___jp_2287_;
}
else
{
lean_object* v___x_2314_; 
lean_inc_ref(v_code_2286_);
v___x_2314_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2309_, v_code_2286_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2309_, v_code_2286_, v___y_2264_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref_known(v___x_2316_, 1);
v___x_2317_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2261_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref_known(v___x_2317_, 1);
v___x_2318_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2315_);
lean_inc_ref(v_a_2271_);
v___x_2319_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2271_, v___x_2318_);
v_a_2273_ = v___x_2319_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2320_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2317_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2317_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2328_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2316_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2316_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2336_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2314_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2314_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
v___jp_2344_:
{
if (lean_obj_tag(v_code_2286_) == 6)
{
v___y_2311_ = v_a_2345_;
v___y_2312_ = v___x_2269_;
goto v___jp_2310_;
}
else
{
v___y_2311_ = v_a_2345_;
v___y_2312_ = v___y_2257_;
goto v___jp_2310_;
}
}
}
else
{
lean_object* v_code_2362_; lean_object* v___x_2363_; 
v_code_2362_ = lean_ctor_get(v_a_2271_, 0);
lean_inc_ref(v___y_2265_);
lean_inc_ref(v_code_2362_);
v___x_2363_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2362_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
lean_inc_ref(v_a_2271_);
v___x_2365_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2271_, v_a_2364_);
v_a_2273_ = v___x_2365_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v_as_2259_);
lean_dec(v_i_2258_);
lean_dec(v_fvarId_2256_);
v_a_2366_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2363_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2363_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
v___jp_2272_:
{
size_t v___x_2274_; size_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = lean_ptr_addr(v_a_2271_);
v___x_2275_ = lean_ptr_addr(v_a_2273_);
v___x_2276_ = lean_usize_dec_eq(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_add(v_i_2258_, v___x_2277_);
v___x_2279_ = lean_array_fset(v_as_2259_, v_i_2258_, v_a_2273_);
lean_dec(v_i_2258_);
v_i_2258_ = v___x_2278_;
v_as_2259_ = v___x_2279_;
goto _start;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec_ref(v_a_2273_);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_add(v_i_2258_, v___x_2281_);
lean_dec(v_i_2258_);
v_i_2258_ = v___x_2282_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2421_; lean_object* v___y_2422_; lean_object* v_decl_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; uint8_t v___y_2472_; lean_object* v___y_2473_; lean_object* v_decl_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2493_; lean_object* v_decl_2494_; lean_object* v_k_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2568_; lean_object* v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v_decl_2764_; lean_object* v_fvarId_2765_; lean_object* v_type_2766_; lean_object* v_value_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2857_; lean_object* v___y_2858_; uint8_t v___y_2859_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; uint8_t v___y_2951_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; uint8_t v___y_3048_; uint8_t v_a_3049_; uint8_t v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v_fileName_3281_; lean_object* v_fileMap_3282_; lean_object* v_options_3283_; lean_object* v_currRecDepth_3284_; lean_object* v_maxRecDepth_3285_; lean_object* v_ref_3286_; lean_object* v_currNamespace_3287_; lean_object* v_openDecls_3288_; lean_object* v_initHeartbeats_3289_; lean_object* v_maxHeartbeats_3290_; lean_object* v_quotContext_3291_; lean_object* v_currMacroScope_3292_; uint8_t v_diag_3293_; lean_object* v_cancelTk_x3f_3294_; uint8_t v_suppressElabErrors_3295_; lean_object* v_inheritedTraceOptions_3296_; uint8_t v___y_3298_; lean_object* v___x_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; 
v_fileName_3281_ = lean_ctor_get(v_a_2381_, 0);
v_fileMap_3282_ = lean_ctor_get(v_a_2381_, 1);
v_options_3283_ = lean_ctor_get(v_a_2381_, 2);
v_currRecDepth_3284_ = lean_ctor_get(v_a_2381_, 3);
v_maxRecDepth_3285_ = lean_ctor_get(v_a_2381_, 4);
v_ref_3286_ = lean_ctor_get(v_a_2381_, 5);
v_currNamespace_3287_ = lean_ctor_get(v_a_2381_, 6);
v_openDecls_3288_ = lean_ctor_get(v_a_2381_, 7);
v_initHeartbeats_3289_ = lean_ctor_get(v_a_2381_, 8);
v_maxHeartbeats_3290_ = lean_ctor_get(v_a_2381_, 9);
v_quotContext_3291_ = lean_ctor_get(v_a_2381_, 10);
v_currMacroScope_3292_ = lean_ctor_get(v_a_2381_, 11);
v_diag_3293_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*14);
v_cancelTk_x3f_3294_ = lean_ctor_get(v_a_2381_, 12);
v_suppressElabErrors_3295_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3296_ = lean_ctor_get(v_a_2381_, 13);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_nat_dec_eq(v_maxRecDepth_3285_, v___x_3328_);
v___x_3330_ = lean_bool_not(v___x_3329_);
if (v___x_3330_ == 0)
{
v___y_3298_ = v___x_3330_;
goto v___jp_3297_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_eq(v_currRecDepth_3284_, v_maxRecDepth_3285_);
v___y_3298_ = v___x_3331_;
goto v___jp_3297_;
}
v___jp_2384_:
{
if (v___y_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v_code_2375_);
v___x_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2385_);
lean_ctor_set(v___x_2388_, 1, v___y_2386_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
else
{
lean_object* v___x_2390_; 
lean_dec_ref(v___y_2386_);
lean_dec_ref(v___y_2385_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_code_2375_);
return v___x_2390_;
}
}
v___jp_2391_:
{
if (v___y_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref(v_code_2375_);
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___y_2392_);
lean_ctor_set(v___x_2395_, 1, v___y_2393_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; 
lean_dec_ref(v___y_2393_);
lean_dec_ref(v___y_2392_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_code_2375_);
return v___x_2397_;
}
}
v___jp_2398_:
{
switch(lean_obj_tag(v_code_2375_))
{
case 1:
{
lean_object* v_decl_2401_; lean_object* v_k_2402_; size_t v___x_2403_; size_t v___x_2404_; uint8_t v___x_2405_; 
v_decl_2401_ = lean_ctor_get(v_code_2375_, 0);
v_k_2402_ = lean_ctor_get(v_code_2375_, 1);
v___x_2403_ = lean_ptr_addr(v_k_2402_);
v___x_2404_ = lean_ptr_addr(v___y_2400_);
v___x_2405_ = lean_usize_dec_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
v___y_2385_ = v___y_2399_;
v___y_2386_ = v___y_2400_;
v___y_2387_ = v___x_2405_;
goto v___jp_2384_;
}
else
{
size_t v___x_2406_; size_t v___x_2407_; uint8_t v___x_2408_; 
v___x_2406_ = lean_ptr_addr(v_decl_2401_);
v___x_2407_ = lean_ptr_addr(v___y_2399_);
v___x_2408_ = lean_usize_dec_eq(v___x_2406_, v___x_2407_);
v___y_2385_ = v___y_2399_;
v___y_2386_ = v___y_2400_;
v___y_2387_ = v___x_2408_;
goto v___jp_2384_;
}
}
case 2:
{
lean_object* v_decl_2409_; lean_object* v_k_2410_; size_t v___x_2411_; size_t v___x_2412_; uint8_t v___x_2413_; 
v_decl_2409_ = lean_ctor_get(v_code_2375_, 0);
v_k_2410_ = lean_ctor_get(v_code_2375_, 1);
v___x_2411_ = lean_ptr_addr(v_k_2410_);
v___x_2412_ = lean_ptr_addr(v___y_2400_);
v___x_2413_ = lean_usize_dec_eq(v___x_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2400_;
v___y_2394_ = v___x_2413_;
goto v___jp_2391_;
}
else
{
size_t v___x_2414_; size_t v___x_2415_; uint8_t v___x_2416_; 
v___x_2414_ = lean_ptr_addr(v_decl_2409_);
v___x_2415_ = lean_ptr_addr(v___y_2399_);
v___x_2416_ = lean_usize_dec_eq(v___x_2414_, v___x_2415_);
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___y_2400_;
v___y_2394_ = v___x_2416_;
goto v___jp_2391_;
}
}
default: 
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_code_2375_);
v___x_2417_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2418_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
}
v___jp_2420_:
{
lean_object* v___x_2431_; 
lean_inc_ref(v___y_2429_);
v___x_2431_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2422_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v_fvarId_2433_; lean_object* v___x_2434_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v_fvarId_2433_ = lean_ctor_get(v_decl_2423_, 0);
v___x_2434_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2433_, v___y_2425_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; uint8_t v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = lean_unbox(v_a_2435_);
lean_dec(v_a_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_code_2375_);
v___x_2437_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2423_, v___y_2425_, v___y_2428_);
lean_dec_ref(v_decl_2423_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2445_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2432_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2432_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2432_);
v_a_2446_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2437_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2437_);
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
if (v___y_2421_ == 0)
{
lean_dec_ref(v___y_2429_);
v___y_2399_ = v_decl_2423_;
v___y_2400_ = v_a_2432_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2454_; 
lean_inc_ref(v_decl_2423_);
v___x_2454_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v___y_2429_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref_known(v___x_2454_, 1);
v___y_2399_ = v_decl_2423_;
v___y_2400_ = v_a_2432_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_a_2432_);
lean_dec_ref(v_decl_2423_);
lean_dec_ref(v_code_2375_);
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2432_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_decl_2423_);
lean_dec_ref(v_code_2375_);
v_a_2463_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2434_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2434_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_decl_2423_);
lean_dec_ref(v_code_2375_);
return v___x_2431_;
}
}
v___jp_2471_:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___y_2421_ = v___y_2472_;
v___y_2422_ = v___y_2473_;
v_decl_2423_ = v_a_2483_;
v___y_2424_ = v___y_2475_;
v___y_2425_ = v___y_2476_;
v___y_2426_ = v___y_2477_;
v___y_2427_ = v___y_2478_;
v___y_2428_ = v___y_2479_;
v___y_2429_ = v___y_2480_;
v___y_2430_ = v___y_2481_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_code_2375_);
v_a_2484_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
v___jp_2492_:
{
lean_object* v_fvarId_2503_; lean_object* v_params_2504_; lean_object* v_type_2505_; lean_object* v___x_2506_; 
v_fvarId_2503_ = lean_ctor_get(v_decl_2494_, 0);
v_params_2504_ = lean_ctor_get(v_decl_2494_, 2);
v_type_2505_ = lean_ctor_get(v_decl_2494_, 3);
v___x_2506_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2503_, v___y_2497_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; uint8_t v___x_2508_; uint8_t v___x_2509_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = 0;
v___x_2509_ = lean_unbox(v_a_2507_);
if (v___x_2509_ == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2375_);
if (v___x_2510_ == 0)
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2472_ = v___x_2511_;
v___y_2473_ = v_k_2495_;
v_decl_2474_ = v_decl_2494_;
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2501_;
v___y_2481_ = v___y_2502_;
goto v___jp_2471_;
}
else
{
uint8_t v___x_2512_; 
lean_inc_ref(v_type_2505_);
v___x_2512_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2505_, v_params_2504_);
if (v___x_2512_ == 0)
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2472_ = v___x_2513_;
v___y_2473_ = v_k_2495_;
v_decl_2474_ = v_decl_2494_;
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2501_;
v___y_2481_ = v___y_2502_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2514_; lean_object* v_subst_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_st_ref_get(v___y_2497_);
v_subst_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_ref(v_subst_2515_);
lean_dec(v___x_2514_);
v___x_2516_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2508_, v___y_2493_, v_decl_2494_, v_subst_2515_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec_ref(v_subst_2515_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2517_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2497_);
if (lean_obj_tag(v___x_2520_) == 0)
{
uint8_t v___x_2521_; 
lean_dec_ref_known(v___x_2520_, 1);
v___x_2521_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2472_ = v___x_2521_;
v___y_2473_ = v_k_2495_;
v_decl_2474_ = v_a_2519_;
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2501_;
v___y_2481_ = v___y_2502_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_a_2519_);
lean_dec(v_a_2507_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_code_2375_);
v_a_2522_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2520_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2520_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_a_2507_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_code_2375_);
v_a_2530_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2518_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2518_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2507_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_code_2375_);
v_a_2538_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2516_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2516_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v_subst_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_st_ref_get(v___y_2497_);
v_subst_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref(v_subst_2547_);
lean_dec(v___x_2546_);
v___x_2548_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2508_, v___y_2493_, v_decl_2494_, v_subst_2547_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec_ref(v_subst_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2421_ = v___x_2550_;
v___y_2422_ = v_k_2495_;
v_decl_2423_ = v_a_2549_;
v___y_2424_ = v___y_2496_;
v___y_2425_ = v___y_2497_;
v___y_2426_ = v___y_2498_;
v___y_2427_ = v___y_2499_;
v___y_2428_ = v___y_2500_;
v___y_2429_ = v___y_2501_;
v___y_2430_ = v___y_2502_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2507_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_code_2375_);
v_a_2551_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2548_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_decl_2494_);
lean_dec_ref(v_code_2375_);
v_a_2559_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2506_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2506_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
v___jp_2567_:
{
if (v___y_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v_code_2375_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2568_);
lean_ctor_set(v___x_2571_, 1, v___y_2569_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; 
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___y_2568_);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_code_2375_);
return v___x_2573_;
}
}
v___jp_2574_:
{
lean_object* v___x_2585_; 
lean_inc_ref(v___y_2580_);
v___x_2585_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2580_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
if (lean_obj_tag(v_a_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v___x_2588_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_val_2587_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v_a_2586_, 1);
v___x_2588_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2584_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref_known(v___x_2588_, 1);
lean_inc_ref(v___y_2582_);
v___x_2589_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2581_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2587_, v_a_2590_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
lean_dec_ref(v___y_2582_);
lean_dec(v_val_2587_);
return v___x_2591_;
}
else
{
lean_dec(v_val_2587_);
lean_dec_ref(v___y_2582_);
return v___x_2589_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_val_2587_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
v_a_2592_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2588_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2588_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; 
lean_dec(v_a_2586_);
lean_inc_ref(v___y_2580_);
v___x_2600_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2580_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
if (lean_obj_tag(v_a_2601_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2603_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_val_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v_a_2601_, 1);
v___x_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_val_2602_);
lean_ctor_set(v___x_2603_, 1, v___y_2581_);
v_code_2375_ = v___x_2603_;
v_a_2376_ = v___y_2579_;
v_a_2377_ = v___y_2584_;
v_a_2378_ = v___y_2578_;
v_a_2379_ = v___y_2575_;
v_a_2380_ = v___y_2577_;
v_a_2381_ = v___y_2582_;
v_a_2382_ = v___y_2576_;
goto _start;
}
else
{
lean_object* v_fvarId_2605_; lean_object* v_value_2606_; lean_object* v___x_2607_; 
lean_dec(v_a_2601_);
v_fvarId_2605_ = lean_ctor_get(v___y_2580_, 0);
v_value_2606_ = lean_ctor_get(v___y_2580_, 3);
v___x_2607_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
if (lean_obj_tag(v_a_2608_) == 1)
{
lean_object* v_val_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_code_2375_);
v_val_2609_ = lean_ctor_get(v_a_2608_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v_a_2608_, 1);
lean_inc(v_fvarId_2605_);
v___x_2610_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2605_, v_val_2609_, v___y_2584_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2611_; 
lean_dec_ref_known(v___x_2610_, 1);
v___x_2611_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2580_, v___y_2584_, v___y_2577_);
lean_dec_ref(v___y_2580_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_dec_ref_known(v___x_2611_, 1);
v_code_2375_ = v___y_2581_;
v_a_2376_ = v___y_2579_;
v_a_2377_ = v___y_2584_;
v_a_2378_ = v___y_2578_;
v_a_2379_ = v___y_2575_;
v_a_2380_ = v___y_2577_;
v_a_2381_ = v___y_2582_;
v_a_2382_ = v___y_2576_;
goto _start;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
v_a_2613_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2611_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2611_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
v_a_2621_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2610_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2610_);
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
lean_object* v___x_2629_; 
lean_dec(v_a_2608_);
lean_inc_ref(v___y_2581_);
lean_inc_ref(v___y_2580_);
v___x_2629_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2580_, v___y_2581_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
if (lean_obj_tag(v_a_2630_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2375_);
v_val_2631_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v_a_2630_, 1);
v___x_2632_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2580_, v___y_2584_, v___y_2577_);
lean_dec_ref(v___y_2580_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; 
v_unused_2640_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2640_);
v___x_2634_ = v___x_2632_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_dec(v___x_2632_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_val_2631_);
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_val_2631_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_val_2631_);
v_a_2641_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2632_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2632_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v___x_2649_; 
lean_dec(v_a_2630_);
lean_inc(v_value_2606_);
v___x_2649_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2606_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
if (lean_obj_tag(v_a_2650_) == 1)
{
lean_object* v_val_2651_; lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2654_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_code_2375_);
v_val_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v_a_2650_, 1);
v_fst_2652_ = lean_ctor_get(v_val_2651_, 0);
lean_inc(v_fst_2652_);
v_snd_2653_ = lean_ctor_get(v_val_2651_, 1);
lean_inc(v_snd_2653_);
lean_dec(v_val_2651_);
lean_inc(v_fvarId_2605_);
v___x_2654_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2605_, v_snd_2653_, v___y_2584_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2654_, 1);
v___x_2655_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2580_, v___y_2584_, v___y_2577_);
lean_dec_ref(v___y_2580_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref_known(v___x_2655_, 1);
lean_inc_ref(v___y_2582_);
v___x_2656_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2581_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2652_, v_a_2657_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
lean_dec_ref(v___y_2582_);
lean_dec(v_fst_2652_);
return v___x_2658_;
}
else
{
lean_dec(v_fst_2652_);
lean_dec_ref(v___y_2582_);
return v___x_2656_;
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_fst_2652_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
v_a_2659_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2655_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_fst_2652_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
v_a_2667_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2654_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2654_);
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
lean_object* v___x_2675_; 
lean_dec(v_a_2650_);
lean_inc_ref(v___y_2582_);
lean_inc_ref(v___y_2581_);
v___x_2675_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2581_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2605_, v___y_2584_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; uint8_t v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = lean_unbox(v_a_2678_);
lean_dec(v_a_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2375_);
v___x_2680_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2580_, v___y_2584_, v___y_2577_);
lean_dec_ref(v___y_2580_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2680_, 0);
lean_dec(v_unused_2688_);
v___x_2682_ = v___x_2680_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v___x_2680_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v_a_2676_);
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2676_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2676_);
v_a_2689_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2680_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2680_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v___x_2697_; 
lean_inc_ref(v___y_2580_);
v___x_2697_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2580_, v___y_2579_, v___y_2584_, v___y_2578_, v___y_2575_, v___y_2577_, v___y_2582_, v___y_2576_);
lean_dec_ref(v___y_2582_);
if (lean_obj_tag(v___x_2697_) == 0)
{
size_t v___x_2698_; size_t v___x_2699_; uint8_t v___x_2700_; 
lean_dec_ref_known(v___x_2697_, 1);
v___x_2698_ = lean_ptr_addr(v___y_2581_);
lean_dec_ref(v___y_2581_);
v___x_2699_ = lean_ptr_addr(v_a_2676_);
v___x_2700_ = lean_usize_dec_eq(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v___y_2583_);
v___y_2568_ = v___y_2580_;
v___y_2569_ = v_a_2676_;
v___y_2570_ = v___x_2700_;
goto v___jp_2567_;
}
else
{
size_t v___x_2701_; size_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_ptr_addr(v___y_2583_);
lean_dec_ref(v___y_2583_);
v___x_2702_ = lean_ptr_addr(v___y_2580_);
v___x_2703_ = lean_usize_dec_eq(v___x_2701_, v___x_2702_);
v___y_2568_ = v___y_2580_;
v___y_2569_ = v_a_2676_;
v___y_2570_ = v___x_2703_;
goto v___jp_2567_;
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2676_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2704_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2697_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2697_);
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
lean_dec(v_a_2676_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2712_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2677_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2677_);
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
else
{
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2720_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2649_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2649_);
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
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2728_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2629_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2629_);
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
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2736_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2607_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2607_);
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
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2744_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2600_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2600_);
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
lean_dec_ref(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_code_2375_);
v_a_2752_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2585_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2585_);
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
v___jp_2760_:
{
uint8_t v___x_2775_; 
v___x_2775_ = l_Lean_Expr_isErased(v_type_2766_);
lean_dec_ref(v_type_2766_);
if (v___x_2775_ == 0)
{
lean_dec(v_value_2767_);
lean_dec(v_fvarId_2765_);
v___y_2575_ = v___y_2771_;
v___y_2576_ = v___y_2774_;
v___y_2577_ = v___y_2772_;
v___y_2578_ = v___y_2770_;
v___y_2579_ = v___y_2768_;
v___y_2580_ = v_decl_2764_;
v___y_2581_ = v___y_2761_;
v___y_2582_ = v___y_2773_;
v___y_2583_ = v___y_2763_;
v___y_2584_ = v___y_2769_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2776_; uint8_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = lean_box(1);
v___x_2777_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2762_, v_value_2767_, v___x_2776_);
lean_dec(v_value_2767_);
v___x_2778_ = lean_bool_not(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_dec(v_fvarId_2765_);
v___y_2575_ = v___y_2771_;
v___y_2576_ = v___y_2774_;
v___y_2577_ = v___y_2772_;
v___y_2578_ = v___y_2770_;
v___y_2579_ = v___y_2768_;
v___y_2580_ = v_decl_2764_;
v___y_2581_ = v___y_2761_;
v___y_2582_ = v___y_2773_;
v___y_2583_ = v___y_2763_;
v___y_2584_ = v___y_2769_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2779_; lean_object* v_subst_2780_; lean_object* v_used_2781_; lean_object* v_binderRenaming_2782_; lean_object* v_funDeclInfoMap_2783_; uint8_t v_simplified_2784_; lean_object* v_visited_2785_; lean_object* v_inline_2786_; lean_object* v_inlineLocal_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref(v___y_2763_);
lean_dec_ref(v_code_2375_);
v___x_2779_ = lean_st_ref_take(v___y_2769_);
v_subst_2780_ = lean_ctor_get(v___x_2779_, 0);
v_used_2781_ = lean_ctor_get(v___x_2779_, 1);
v_binderRenaming_2782_ = lean_ctor_get(v___x_2779_, 2);
v_funDeclInfoMap_2783_ = lean_ctor_get(v___x_2779_, 3);
v_simplified_2784_ = lean_ctor_get_uint8(v___x_2779_, sizeof(void*)*7);
v_visited_2785_ = lean_ctor_get(v___x_2779_, 4);
v_inline_2786_ = lean_ctor_get(v___x_2779_, 5);
v_inlineLocal_2787_ = lean_ctor_get(v___x_2779_, 6);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2789_ = v___x_2779_;
v_isShared_2790_ = v_isSharedCheck_2807_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_inlineLocal_2787_);
lean_inc(v_inline_2786_);
lean_inc(v_visited_2785_);
lean_inc(v_funDeclInfoMap_2783_);
lean_inc(v_binderRenaming_2782_);
lean_inc(v_used_2781_);
lean_inc(v_subst_2780_);
lean_dec(v___x_2779_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2807_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2791_ = lean_box(0);
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2780_, v_fvarId_2765_, v___x_2791_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2792_);
v___x_2794_ = v___x_2789_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_used_2781_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_binderRenaming_2782_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_funDeclInfoMap_2783_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_visited_2785_);
lean_ctor_set(v_reuseFailAlloc_2806_, 5, v_inline_2786_);
lean_ctor_set(v_reuseFailAlloc_2806_, 6, v_inlineLocal_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2806_, sizeof(void*)*7, v_simplified_2784_);
v___x_2794_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_st_ref_set(v___y_2769_, v___x_2794_);
v___x_2796_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2764_, v___y_2769_, v___y_2772_);
lean_dec_ref(v_decl_2764_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_dec_ref_known(v___x_2796_, 1);
v_code_2375_ = v___y_2761_;
v_a_2376_ = v___y_2768_;
v_a_2377_ = v___y_2769_;
v_a_2378_ = v___y_2770_;
v_a_2379_ = v___y_2771_;
v_a_2380_ = v___y_2772_;
v_a_2381_ = v___y_2773_;
v_a_2382_ = v___y_2774_;
goto _start;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec_ref(v___y_2773_);
lean_dec_ref(v___y_2761_);
v_a_2798_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2796_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2796_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
}
}
}
v___jp_2808_:
{
lean_object* v_fvarId_2820_; lean_object* v_type_2821_; lean_object* v_value_2822_; lean_object* v___x_2823_; 
v_fvarId_2820_ = lean_ctor_get(v___y_2811_, 0);
v_type_2821_ = lean_ctor_get(v___y_2811_, 2);
v_value_2822_ = lean_ctor_get(v___y_2811_, 3);
lean_inc(v_value_2822_);
v___x_2823_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2822_, v___y_2813_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
if (lean_obj_tag(v_a_2824_) == 1)
{
lean_object* v_val_2825_; lean_object* v___x_2826_; 
v_val_2825_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_val_2825_);
lean_dec_ref_known(v_a_2824_, 1);
v___x_2826_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2814_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2827_; 
lean_dec_ref_known(v___x_2826_, 1);
v___x_2827_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2810_, v___y_2811_, v_val_2825_, v___y_2817_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v_fvarId_2829_; lean_object* v_type_2830_; lean_object* v_value_2831_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v_fvarId_2829_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_fvarId_2829_);
v_type_2830_ = lean_ctor_get(v_a_2828_, 2);
lean_inc_ref(v_type_2830_);
v_value_2831_ = lean_ctor_get(v_a_2828_, 3);
lean_inc(v_value_2831_);
v___y_2761_ = v___y_2809_;
v___y_2762_ = v___y_2810_;
v___y_2763_ = v___y_2812_;
v_decl_2764_ = v_a_2828_;
v_fvarId_2765_ = v_fvarId_2829_;
v_type_2766_ = v_type_2830_;
v_value_2767_ = v_value_2831_;
v___y_2768_ = v___y_2813_;
v___y_2769_ = v___y_2814_;
v___y_2770_ = v___y_2815_;
v___y_2771_ = v___y_2816_;
v___y_2772_ = v___y_2817_;
v___y_2773_ = v___y_2818_;
v___y_2774_ = v___y_2819_;
goto v___jp_2760_;
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___y_2812_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_code_2375_);
v_a_2832_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2827_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2827_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_val_2825_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_code_2375_);
v_a_2840_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2826_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2826_);
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
lean_inc(v_value_2822_);
lean_inc_ref(v_type_2821_);
lean_inc(v_fvarId_2820_);
lean_dec(v_a_2824_);
v___y_2761_ = v___y_2809_;
v___y_2762_ = v___y_2810_;
v___y_2763_ = v___y_2812_;
v_decl_2764_ = v___y_2811_;
v_fvarId_2765_ = v_fvarId_2820_;
v_type_2766_ = v_type_2821_;
v_value_2767_ = v_value_2822_;
v___y_2768_ = v___y_2813_;
v___y_2769_ = v___y_2814_;
v___y_2770_ = v___y_2815_;
v___y_2771_ = v___y_2816_;
v___y_2772_ = v___y_2817_;
v___y_2773_ = v___y_2818_;
v___y_2774_ = v___y_2819_;
goto v___jp_2760_;
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_code_2375_);
v_a_2848_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2823_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2823_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
v___jp_2856_:
{
if (v___y_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec_ref(v_code_2375_);
v___x_2860_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2857_);
lean_ctor_set(v___x_2860_, 1, v___y_2858_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
else
{
lean_object* v___x_2862_; 
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v_code_2375_);
return v___x_2862_;
}
}
v___jp_2863_:
{
uint8_t v___x_2868_; 
v___x_2868_ = l_Lean_instBEqFVarId_beq(v___y_2866_, v___y_2864_);
lean_dec(v___y_2866_);
if (v___x_2868_ == 0)
{
lean_dec_ref(v___y_2865_);
v___y_2857_ = v___y_2864_;
v___y_2858_ = v___y_2867_;
v___y_2859_ = v___x_2868_;
goto v___jp_2856_;
}
else
{
size_t v___x_2869_; size_t v___x_2870_; uint8_t v___x_2871_; 
v___x_2869_ = lean_ptr_addr(v___y_2865_);
lean_dec_ref(v___y_2865_);
v___x_2870_ = lean_ptr_addr(v___y_2867_);
v___x_2871_ = lean_usize_dec_eq(v___x_2869_, v___x_2870_);
v___y_2857_ = v___y_2864_;
v___y_2858_ = v___y_2867_;
v___y_2859_ = v___x_2871_;
goto v___jp_2856_;
}
}
v___jp_2872_:
{
if (lean_obj_tag(v___y_2877_) == 0)
{
lean_dec_ref_known(v___y_2877_, 1);
v___y_2864_ = v___y_2873_;
v___y_2865_ = v___y_2874_;
v___y_2866_ = v___y_2875_;
v___y_2867_ = v___y_2876_;
goto v___jp_2863_;
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v_code_2375_);
v_a_2878_ = lean_ctor_get(v___y_2877_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___y_2877_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___y_2877_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___y_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
v___jp_2886_:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2887_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2898_);
v___x_2891_ = v___x_2889_;
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v___x_2889_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___y_2888_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2895_ = v___x_2891_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v___y_2888_);
v_a_2899_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2889_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2889_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
v___jp_2907_:
{
if (lean_obj_tag(v___y_2910_) == 0)
{
lean_dec_ref_known(v___y_2910_, 1);
v___y_2887_ = v___y_2908_;
v___y_2888_ = v___y_2909_;
goto v___jp_2886_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v___y_2909_);
v_a_2911_ = lean_ctor_get(v___y_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___y_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___y_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___y_2910_);
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
v___jp_2919_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2921_);
lean_ctor_set(v___x_2924_, 1, v___y_2923_);
lean_ctor_set(v___x_2924_, 2, v___y_2922_);
lean_ctor_set(v___x_2924_, 3, v___y_2920_);
v___x_2925_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
v___jp_2927_:
{
if (v___y_2933_ == 0)
{
lean_dec(v___y_2932_);
lean_dec_ref(v_code_2375_);
v___y_2920_ = v___y_2929_;
v___y_2921_ = v___y_2928_;
v___y_2922_ = v___y_2931_;
v___y_2923_ = v___y_2930_;
goto v___jp_2919_;
}
else
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_instBEqFVarId_beq(v___y_2932_, v___y_2931_);
lean_dec(v___y_2932_);
if (v___x_2934_ == 0)
{
lean_dec_ref(v_code_2375_);
v___y_2920_ = v___y_2929_;
v___y_2921_ = v___y_2928_;
v___y_2922_ = v___y_2931_;
v___y_2923_ = v___y_2930_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2935_; 
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_code_2375_);
return v___x_2935_;
}
}
}
v___jp_2936_:
{
if (v___y_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v___y_2949_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2937_);
lean_inc(v___y_2946_);
v___x_2952_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2946_, v___y_2945_);
if (lean_obj_tag(v___x_2952_) == 0)
{
size_t v___x_2953_; size_t v___x_2954_; uint8_t v___x_2955_; 
lean_dec_ref_known(v___x_2952_, 1);
v___x_2953_ = lean_ptr_addr(v___y_2944_);
lean_dec_ref(v___y_2944_);
v___x_2954_ = lean_ptr_addr(v___y_2938_);
v___x_2955_ = lean_usize_dec_eq(v___x_2953_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_dec_ref(v___y_2941_);
v___y_2928_ = v___y_2939_;
v___y_2929_ = v___y_2938_;
v___y_2930_ = v___y_2947_;
v___y_2931_ = v___y_2946_;
v___y_2932_ = v___y_2942_;
v___y_2933_ = v___x_2955_;
goto v___jp_2927_;
}
else
{
size_t v___x_2956_; size_t v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_ptr_addr(v___y_2941_);
lean_dec_ref(v___y_2941_);
v___x_2957_ = lean_ptr_addr(v___y_2947_);
v___x_2958_ = lean_usize_dec_eq(v___x_2956_, v___x_2957_);
v___y_2928_ = v___y_2939_;
v___y_2929_ = v___y_2938_;
v___y_2930_ = v___y_2947_;
v___y_2931_ = v___y_2946_;
v___y_2932_ = v___y_2942_;
v___y_2933_ = v___x_2958_;
goto v___jp_2927_;
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v_code_2375_);
v_a_2959_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2952_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2952_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
uint8_t v___x_2967_; 
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2375_);
v___x_2967_ = lean_nat_dec_lt(v___y_2949_, v___y_2940_);
lean_dec(v___y_2949_);
if (v___x_2967_ == 0)
{
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v___y_2937_);
v___y_2887_ = v___y_2945_;
v___y_2888_ = v___y_2947_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_nat_dec_le(v___y_2940_, v___y_2940_);
if (v___x_2969_ == 0)
{
if (v___x_2967_ == 0)
{
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v___y_2937_);
v___y_2887_ = v___y_2945_;
v___y_2888_ = v___y_2947_;
goto v___jp_2886_;
}
else
{
size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = lean_usize_of_nat(v___y_2940_);
lean_dec(v___y_2940_);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2938_, v___x_2970_, v___x_2971_, v___x_2968_, v___y_2948_, v___y_2943_, v___y_2937_, v___y_2950_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2938_);
v___y_2908_ = v___y_2945_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___x_2972_;
goto v___jp_2907_;
}
}
else
{
size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___y_2940_);
lean_dec(v___y_2940_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2938_, v___x_2973_, v___x_2974_, v___x_2968_, v___y_2948_, v___y_2943_, v___y_2937_, v___y_2950_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2938_);
v___y_2908_ = v___y_2945_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___x_2975_;
goto v___jp_2907_;
}
}
}
}
v___jp_2976_:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = lean_array_get_size(v___y_2978_);
v___x_2992_ = lean_nat_dec_lt(v___y_2982_, v___x_2991_);
if (v___x_2992_ == 0)
{
uint8_t v___x_2993_; 
v___x_2993_ = lean_bool_not(v___y_2984_);
v___y_2937_ = v___y_2989_;
v___y_2938_ = v___y_2978_;
v___y_2939_ = v___y_2977_;
v___y_2940_ = v___x_2991_;
v___y_2941_ = v___y_2983_;
v___y_2942_ = v___y_2985_;
v___y_2943_ = v___y_2988_;
v___y_2944_ = v___y_2979_;
v___y_2945_ = v___y_2986_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___y_2987_;
v___y_2949_ = v___y_2982_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___x_2993_;
goto v___jp_2936_;
}
else
{
if (v___x_2992_ == 0)
{
uint8_t v___x_2994_; 
v___x_2994_ = lean_bool_not(v___y_2984_);
v___y_2937_ = v___y_2989_;
v___y_2938_ = v___y_2978_;
v___y_2939_ = v___y_2977_;
v___y_2940_ = v___x_2991_;
v___y_2941_ = v___y_2983_;
v___y_2942_ = v___y_2985_;
v___y_2943_ = v___y_2988_;
v___y_2944_ = v___y_2979_;
v___y_2945_ = v___y_2986_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___y_2987_;
v___y_2949_ = v___y_2982_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___x_2994_;
goto v___jp_2936_;
}
else
{
size_t v___x_2995_; size_t v___x_2996_; uint8_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = lean_usize_of_nat(v___x_2991_);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2984_, v___y_2978_, v___x_2995_, v___x_2996_);
v___x_2998_ = lean_bool_not(v___x_2997_);
v___y_2937_ = v___y_2989_;
v___y_2938_ = v___y_2978_;
v___y_2939_ = v___y_2977_;
v___y_2940_ = v___x_2991_;
v___y_2941_ = v___y_2983_;
v___y_2942_ = v___y_2985_;
v___y_2943_ = v___y_2988_;
v___y_2944_ = v___y_2979_;
v___y_2945_ = v___y_2986_;
v___y_2946_ = v___y_2980_;
v___y_2947_ = v___y_2981_;
v___y_2948_ = v___y_2987_;
v___y_2949_ = v___y_2982_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___x_2998_;
goto v___jp_2936_;
}
}
}
v___jp_2999_:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v___x_3002_, 0);
lean_dec(v_unused_3010_);
v___x_3004_ = v___x_3002_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_dec(v___x_3002_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___y_3000_);
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___y_3000_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v___y_3000_);
v_a_3011_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3002_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3002_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
v___jp_3019_:
{
if (lean_obj_tag(v___y_3022_) == 0)
{
lean_dec_ref_known(v___y_3022_, 1);
v___y_3000_ = v___y_3020_;
v___y_3001_ = v___y_3021_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v___y_3020_);
v_a_3023_ = lean_ctor_get(v___y_3022_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___y_3022_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___y_3022_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___y_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
v___jp_3031_:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_bool_not(v_a_3049_);
if (v___x_3050_ == 0)
{
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec_ref(v___y_3036_);
v___y_2977_ = v___y_3033_;
v___y_2978_ = v___y_3034_;
v___y_2979_ = v___y_3041_;
v___y_2980_ = v___y_3045_;
v___y_2981_ = v___y_3046_;
v___y_2982_ = v___y_3047_;
v___y_2983_ = v___y_3039_;
v___y_2984_ = v___y_3048_;
v___y_2985_ = v___y_3040_;
v___y_2986_ = v___y_3037_;
v___y_2987_ = v___y_3032_;
v___y_2988_ = v___y_3038_;
v___y_2989_ = v___y_3035_;
v___y_2990_ = v___y_3044_;
goto v___jp_2976_;
}
else
{
uint8_t v___x_3051_; 
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v_code_2375_);
v___x_3051_ = lean_nat_dec_lt(v___y_3047_, v___y_3043_);
lean_dec(v___y_3047_);
if (v___x_3051_ == 0)
{
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3036_);
v___y_3000_ = v___y_3042_;
v___y_3001_ = v___y_3037_;
goto v___jp_2999_;
}
else
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_nat_dec_le(v___y_3043_, v___y_3043_);
if (v___x_3053_ == 0)
{
if (v___x_3051_ == 0)
{
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3036_);
v___y_3000_ = v___y_3042_;
v___y_3001_ = v___y_3037_;
goto v___jp_2999_;
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_of_nat(v___y_3043_);
lean_dec(v___y_3043_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3036_, v___x_3054_, v___x_3055_, v___x_3052_, v___y_3038_);
lean_dec_ref(v___y_3036_);
v___y_3020_ = v___y_3042_;
v___y_3021_ = v___y_3037_;
v___y_3022_ = v___x_3056_;
goto v___jp_3019_;
}
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___y_3043_);
lean_dec(v___y_3043_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3036_, v___x_3057_, v___x_3058_, v___x_3052_, v___y_3038_);
lean_dec_ref(v___y_3036_);
v___y_3020_ = v___y_3042_;
v___y_3021_ = v___y_3037_;
v___y_3022_ = v___x_3059_;
goto v___jp_3019_;
}
}
}
}
v___jp_3060_:
{
switch(lean_obj_tag(v_code_2375_))
{
case 0:
{
lean_object* v_decl_3069_; lean_object* v_k_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
v_decl_3069_ = lean_ctor_get(v_code_2375_, 0);
v_k_3070_ = lean_ctor_get(v_code_2375_, 1);
v___x_3071_ = 0;
lean_inc_ref(v_decl_3069_);
v___x_3072_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3071_, v___y_3061_, v_decl_3069_, v___y_3063_, v___y_3066_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; uint8_t v___x_3074_; uint8_t v___x_3075_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3071_, v_decl_3069_, v_a_3073_);
v___x_3075_ = lean_bool_not(v___x_3074_);
if (v___x_3075_ == 0)
{
lean_inc_ref(v_decl_3069_);
lean_inc_ref(v_k_3070_);
v___y_2809_ = v_k_3070_;
v___y_2810_ = v___x_3071_;
v___y_2811_ = v_a_3073_;
v___y_2812_ = v_decl_3069_;
v___y_2813_ = v___y_3062_;
v___y_2814_ = v___y_3063_;
v___y_2815_ = v___y_3064_;
v___y_2816_ = v___y_3065_;
v___y_2817_ = v___y_3066_;
v___y_2818_ = v___y_3067_;
v___y_2819_ = v___y_3068_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3063_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_dec_ref_known(v___x_3076_, 1);
lean_inc_ref(v_decl_3069_);
lean_inc_ref(v_k_3070_);
v___y_2809_ = v_k_3070_;
v___y_2810_ = v___x_3071_;
v___y_2811_ = v_a_3073_;
v___y_2812_ = v_decl_3069_;
v___y_2813_ = v___y_3062_;
v___y_2814_ = v___y_3063_;
v___y_2815_ = v___y_3064_;
v___y_2816_ = v___y_3065_;
v___y_2817_ = v___y_3066_;
v___y_2818_ = v___y_3067_;
v___y_2819_ = v___y_3068_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_a_3073_);
lean_dec_ref_known(v_code_2375_, 2);
lean_dec_ref(v___y_3067_);
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3076_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3076_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref_known(v_code_2375_, 2);
lean_dec_ref(v___y_3067_);
v_a_3085_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3072_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3072_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3093_; lean_object* v_args_3094_; lean_object* v___x_3095_; lean_object* v_subst_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; 
v_fvarId_3093_ = lean_ctor_get(v_code_2375_, 0);
v_args_3094_ = lean_ctor_get(v_code_2375_, 1);
v___x_3095_ = lean_st_ref_get(v___y_3063_);
v_subst_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc_ref(v_subst_3096_);
lean_dec(v___x_3095_);
v___x_3097_ = 0;
lean_inc(v_fvarId_3093_);
v___x_3098_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3096_, v_fvarId_3093_, v___y_3061_);
lean_dec_ref(v_subst_3096_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_fvarId_3099_; lean_object* v___x_3100_; 
v_fvarId_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_fvarId_3099_);
lean_dec_ref_known(v___x_3098_, 1);
lean_inc_ref(v_args_3094_);
v___x_3100_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3097_, v___y_3061_, v_args_3094_, v___y_3063_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_n(v_a_3101_, 2);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3099_, v_a_3101_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
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
lean_dec_ref_known(v_code_2375_, 2);
v_val_3104_ = lean_ctor_get(v_a_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v_a_3103_, 1);
v_code_2375_ = v_val_3104_;
v_a_2376_ = v___y_3062_;
v_a_2377_ = v___y_3063_;
v_a_2378_ = v___y_3064_;
v_a_2379_ = v___y_3065_;
v_a_2380_ = v___y_3066_;
v_a_2381_ = v___y_3067_;
v_a_2382_ = v___y_3068_;
goto _start;
}
else
{
lean_object* v___x_3106_; 
lean_dec(v_a_3103_);
lean_dec_ref(v___y_3067_);
lean_inc(v_fvarId_3099_);
v___x_3106_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3099_, v___y_3063_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
lean_dec_ref_known(v___x_3106_, 1);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_array_get_size(v_a_3101_);
v___x_3109_ = lean_nat_dec_lt(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_inc(v_fvarId_3093_);
lean_inc_ref(v_args_3094_);
v___y_2864_ = v_fvarId_3099_;
v___y_2865_ = v_args_3094_;
v___y_2866_ = v_fvarId_3093_;
v___y_2867_ = v_a_3101_;
goto v___jp_2863_;
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
lean_inc(v_fvarId_3093_);
lean_inc_ref(v_args_3094_);
v___y_2864_ = v_fvarId_3099_;
v___y_2865_ = v_args_3094_;
v___y_2866_ = v_fvarId_3093_;
v___y_2867_ = v_a_3101_;
goto v___jp_2863_;
}
else
{
size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((size_t)0ULL);
v___x_3113_ = lean_usize_of_nat(v___x_3108_);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3101_, v___x_3112_, v___x_3113_, v___x_3110_, v___y_3063_);
lean_inc(v_fvarId_3093_);
lean_inc_ref(v_args_3094_);
v___y_2873_ = v_fvarId_3099_;
v___y_2874_ = v_args_3094_;
v___y_2875_ = v_fvarId_3093_;
v___y_2876_ = v_a_3101_;
v___y_2877_ = v___x_3114_;
goto v___jp_2872_;
}
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = lean_usize_of_nat(v___x_3108_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3101_, v___x_3115_, v___x_3116_, v___x_3110_, v___y_3063_);
lean_inc(v_fvarId_3093_);
lean_inc_ref(v_args_3094_);
v___y_2873_ = v_fvarId_3099_;
v___y_2874_ = v_args_3094_;
v___y_2875_ = v_fvarId_3093_;
v___y_2876_ = v_a_3101_;
v___y_2877_ = v___x_3117_;
goto v___jp_2872_;
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_3101_);
lean_dec(v_fvarId_3099_);
lean_dec_ref_known(v_code_2375_, 2);
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
lean_dec_ref_known(v_code_2375_, 2);
lean_dec_ref(v___y_3067_);
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
lean_dec_ref_known(v_code_2375_, 2);
lean_dec_ref(v___y_3067_);
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
lean_dec_ref_known(v_code_2375_, 2);
v___x_3142_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3097_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec_ref(v___y_3067_);
return v___x_3142_;
}
}
case 4:
{
lean_object* v_cases_3143_; lean_object* v___x_3144_; 
v_cases_3143_ = lean_ctor_get(v_code_2375_, 0);
lean_inc_ref(v_cases_3143_);
v___x_3144_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3143_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3216_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3216_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3216_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
if (lean_obj_tag(v_a_3145_) == 1)
{
lean_object* v_val_3149_; lean_object* v___x_3151_; 
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
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
lean_object* v_typeName_3153_; lean_object* v_resultType_3154_; lean_object* v_discr_3155_; lean_object* v_alts_3156_; lean_object* v___x_3157_; lean_object* v_subst_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; 
lean_del_object(v___x_3147_);
lean_dec(v_a_3145_);
v_typeName_3153_ = lean_ctor_get(v_cases_3143_, 0);
v_resultType_3154_ = lean_ctor_get(v_cases_3143_, 1);
v_discr_3155_ = lean_ctor_get(v_cases_3143_, 2);
v_alts_3156_ = lean_ctor_get(v_cases_3143_, 3);
v___x_3157_ = lean_st_ref_get(v___y_3063_);
v_subst_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc_ref(v_subst_3158_);
lean_dec(v___x_3157_);
v___x_3159_ = 0;
lean_inc(v_discr_3155_);
v___x_3160_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3158_, v_discr_3155_, v___y_3061_);
lean_dec_ref(v_subst_3158_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_fvarId_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_fvarId_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc_n(v_fvarId_3161_, 2);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = lean_st_ref_get(v___y_3063_);
v___x_3163_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3156_);
v___x_3164_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3161_, v___y_3061_, v___x_3163_, v_alts_3156_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3165_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3198_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3198_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3198_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_subst_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_subst_3171_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_subst_3171_);
lean_dec(v___x_3162_);
lean_inc_ref(v_resultType_3154_);
v___x_3172_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3159_, v_subst_3171_, v___y_3061_, v_resultType_3154_);
lean_dec_ref(v_subst_3171_);
v___x_3173_ = lean_array_get_size(v_a_3167_);
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = lean_nat_dec_eq(v___x_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_del_object(v___x_3169_);
lean_inc(v_discr_3155_);
lean_inc_ref(v_resultType_3154_);
lean_inc_ref(v_alts_3156_);
lean_inc(v_typeName_3153_);
v___y_2977_ = v_typeName_3153_;
v___y_2978_ = v_a_3167_;
v___y_2979_ = v_alts_3156_;
v___y_2980_ = v_fvarId_3161_;
v___y_2981_ = v___x_3172_;
v___y_2982_ = v___x_3163_;
v___y_2983_ = v_resultType_3154_;
v___y_2984_ = v___y_3061_;
v___y_2985_ = v_discr_3155_;
v___y_2986_ = v___y_3063_;
v___y_2987_ = v___y_3065_;
v___y_2988_ = v___y_3066_;
v___y_2989_ = v___y_3067_;
v___y_2990_ = v___y_3068_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_array_fget_borrowed(v_a_3167_, v___x_3163_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_params_3177_; lean_object* v_code_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
lean_del_object(v___x_3169_);
v_params_3177_ = lean_ctor_get(v___x_3176_, 1);
lean_inc_ref(v_params_3177_);
v_code_3178_ = lean_ctor_get(v___x_3176_, 2);
lean_inc_ref(v_code_3178_);
v___x_3179_ = lean_array_get_size(v_params_3177_);
v___x_3180_ = lean_nat_dec_lt(v___x_3163_, v___x_3179_);
if (v___x_3180_ == 0)
{
lean_inc_ref(v_alts_3156_);
lean_inc(v_discr_3155_);
lean_inc_ref(v_resultType_3154_);
lean_inc(v_typeName_3153_);
v___y_3032_ = v___y_3065_;
v___y_3033_ = v_typeName_3153_;
v___y_3034_ = v_a_3167_;
v___y_3035_ = v___y_3067_;
v___y_3036_ = v_params_3177_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3066_;
v___y_3039_ = v_resultType_3154_;
v___y_3040_ = v_discr_3155_;
v___y_3041_ = v_alts_3156_;
v___y_3042_ = v_code_3178_;
v___y_3043_ = v___x_3179_;
v___y_3044_ = v___y_3068_;
v___y_3045_ = v_fvarId_3161_;
v___y_3046_ = v___x_3172_;
v___y_3047_ = v___x_3163_;
v___y_3048_ = v___y_3061_;
v_a_3049_ = v___x_3180_;
goto v___jp_3031_;
}
else
{
if (v___x_3180_ == 0)
{
lean_inc_ref(v_alts_3156_);
lean_inc(v_discr_3155_);
lean_inc_ref(v_resultType_3154_);
lean_inc(v_typeName_3153_);
v___y_3032_ = v___y_3065_;
v___y_3033_ = v_typeName_3153_;
v___y_3034_ = v_a_3167_;
v___y_3035_ = v___y_3067_;
v___y_3036_ = v_params_3177_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3066_;
v___y_3039_ = v_resultType_3154_;
v___y_3040_ = v_discr_3155_;
v___y_3041_ = v_alts_3156_;
v___y_3042_ = v_code_3178_;
v___y_3043_ = v___x_3179_;
v___y_3044_ = v___y_3068_;
v___y_3045_ = v_fvarId_3161_;
v___y_3046_ = v___x_3172_;
v___y_3047_ = v___x_3163_;
v___y_3048_ = v___y_3061_;
v_a_3049_ = v___x_3180_;
goto v___jp_3031_;
}
else
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = lean_usize_of_nat(v___x_3179_);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3177_, v___x_3181_, v___x_3182_, v___y_3063_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; uint8_t v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = lean_unbox(v_a_3184_);
lean_dec(v_a_3184_);
lean_inc_ref(v_alts_3156_);
lean_inc(v_discr_3155_);
lean_inc_ref(v_resultType_3154_);
lean_inc(v_typeName_3153_);
v___y_3032_ = v___y_3065_;
v___y_3033_ = v_typeName_3153_;
v___y_3034_ = v_a_3167_;
v___y_3035_ = v___y_3067_;
v___y_3036_ = v_params_3177_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3066_;
v___y_3039_ = v_resultType_3154_;
v___y_3040_ = v_discr_3155_;
v___y_3041_ = v_alts_3156_;
v___y_3042_ = v_code_3178_;
v___y_3043_ = v___x_3179_;
v___y_3044_ = v___y_3068_;
v___y_3045_ = v_fvarId_3161_;
v___y_3046_ = v___x_3172_;
v___y_3047_ = v___x_3163_;
v___y_3048_ = v___y_3061_;
v_a_3049_ = v___x_3185_;
goto v___jp_3031_;
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v_code_3178_);
lean_dec_ref(v_params_3177_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3167_);
lean_dec(v_fvarId_3161_);
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
v_a_3186_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3183_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3183_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
}
else
{
lean_object* v_code_3194_; lean_object* v___x_3196_; 
lean_inc_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3167_);
lean_dec(v_fvarId_3161_);
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
v_code_3194_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_code_3194_);
lean_dec_ref_known(v___x_3176_, 1);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v_code_3194_);
v___x_3196_ = v___x_3169_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_code_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v___x_3162_);
lean_dec(v_fvarId_3161_);
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
v_a_3199_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3166_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3166_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v___x_3162_);
lean_dec(v_fvarId_3161_);
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
v_a_3207_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3164_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3164_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v___x_3215_; 
lean_dec_ref_known(v_code_2375_, 1);
v___x_3215_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3159_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec_ref(v___y_3067_);
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref_known(v_code_2375_, 1);
lean_dec_ref(v___y_3067_);
v_a_3217_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3144_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3144_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3225_; lean_object* v___x_3226_; lean_object* v_subst_3227_; lean_object* v___x_3228_; 
v_fvarId_3225_ = lean_ctor_get(v_code_2375_, 0);
v___x_3226_ = lean_st_ref_get(v___y_3063_);
v_subst_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref(v_subst_3227_);
lean_dec(v___x_3226_);
lean_inc(v_fvarId_3225_);
v___x_3228_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3227_, v_fvarId_3225_, v___y_3061_);
lean_dec_ref(v_subst_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_fvarId_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v___y_3067_);
v_fvarId_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc_n(v_fvarId_3229_, 2);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3229_, v___y_3063_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3249_; 
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3230_, 0);
lean_dec(v_unused_3250_);
v___x_3232_ = v___x_3230_;
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
else
{
lean_dec(v___x_3230_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_instBEqFVarId_beq(v_fvarId_3225_, v_fvarId_3229_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3244_; 
v_isSharedCheck_3244_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_3245_);
v___x_3236_ = v_code_2375_;
v_isShared_3237_ = v_isSharedCheck_3244_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v_code_2375_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3244_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_fvarId_3229_);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_fvarId_3229_);
v___x_3239_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3241_; 
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3239_);
v___x_3241_ = v___x_3232_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v___x_3247_; 
lean_dec(v_fvarId_3229_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v_code_2375_);
v___x_3247_ = v___x_3232_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_code_2375_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_fvarId_3229_);
lean_dec_ref_known(v_code_2375_, 1);
v_a_3251_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3230_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3230_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
uint8_t v___x_3259_; lean_object* v___x_3260_; 
lean_dec_ref_known(v_code_2375_, 1);
v___x_3259_ = 0;
v___x_3260_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3259_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec_ref(v___y_3067_);
return v___x_3260_;
}
}
case 6:
{
lean_object* v_type_3261_; lean_object* v___x_3262_; lean_object* v_subst_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; size_t v___x_3266_; size_t v___x_3267_; uint8_t v___x_3268_; 
lean_dec_ref(v___y_3067_);
v_type_3261_ = lean_ctor_get(v_code_2375_, 0);
v___x_3262_ = lean_st_ref_get(v___y_3063_);
v_subst_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc_ref(v_subst_3263_);
lean_dec(v___x_3262_);
v___x_3264_ = 0;
lean_inc_ref(v_type_3261_);
v___x_3265_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3264_, v_subst_3263_, v___y_3061_, v_type_3261_);
lean_dec_ref(v_subst_3263_);
v___x_3266_ = lean_ptr_addr(v_type_3261_);
v___x_3267_ = lean_ptr_addr(v___x_3265_);
v___x_3268_ = lean_usize_dec_eq(v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3276_; 
v_isSharedCheck_3276_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_3277_);
v___x_3270_ = v_code_2375_;
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
else
{
lean_dec(v_code_2375_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3265_);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3265_);
v___x_3273_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
}
}
else
{
lean_object* v___x_3278_; 
lean_dec_ref(v___x_3265_);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_code_2375_);
return v___x_3278_;
}
}
default: 
{
lean_object* v_decl_3279_; lean_object* v_k_3280_; 
v_decl_3279_ = lean_ctor_get(v_code_2375_, 0);
v_k_3280_ = lean_ctor_get(v_code_2375_, 1);
lean_inc_ref(v_k_3280_);
lean_inc_ref(v_decl_3279_);
v___y_2493_ = v___y_3061_;
v_decl_2494_ = v_decl_3279_;
v_k_2495_ = v_k_3280_;
v___y_2496_ = v___y_3062_;
v___y_2497_ = v___y_3063_;
v___y_2498_ = v___y_3064_;
v___y_2499_ = v___y_3065_;
v___y_2500_ = v___y_3066_;
v___y_2501_ = v___y_3067_;
v___y_2502_ = v___y_3068_;
goto v___jp_2492_;
}
}
}
v___jp_3297_:
{
if (v___y_3298_ == 0)
{
lean_object* v___x_3299_; 
lean_inc_ref(v_inheritedTraceOptions_3296_);
lean_inc(v_cancelTk_x3f_3294_);
lean_inc(v_currMacroScope_3292_);
lean_inc(v_quotContext_3291_);
lean_inc(v_maxHeartbeats_3290_);
lean_inc(v_initHeartbeats_3289_);
lean_inc(v_openDecls_3288_);
lean_inc(v_currNamespace_3287_);
lean_inc(v_ref_3286_);
lean_inc(v_maxRecDepth_3285_);
lean_inc(v_currRecDepth_3284_);
lean_inc_ref(v_options_3283_);
lean_inc_ref(v_fileMap_3282_);
lean_inc_ref(v_fileName_3281_);
lean_dec_ref(v_a_2381_);
v___x_3299_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2377_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; lean_object* v_visited_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
lean_dec_ref_known(v___x_3299_, 1);
v___x_3300_ = lean_st_ref_get(v_a_2377_);
v_visited_3301_ = lean_ctor_get(v___x_3300_, 4);
lean_inc(v_visited_3301_);
lean_dec(v___x_3300_);
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_nat_add(v_currRecDepth_3284_, v___x_3302_);
lean_dec(v_currRecDepth_3284_);
v___x_3304_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3304_, 0, v_fileName_3281_);
lean_ctor_set(v___x_3304_, 1, v_fileMap_3282_);
lean_ctor_set(v___x_3304_, 2, v_options_3283_);
lean_ctor_set(v___x_3304_, 3, v___x_3303_);
lean_ctor_set(v___x_3304_, 4, v_maxRecDepth_3285_);
lean_ctor_set(v___x_3304_, 5, v_ref_3286_);
lean_ctor_set(v___x_3304_, 6, v_currNamespace_3287_);
lean_ctor_set(v___x_3304_, 7, v_openDecls_3288_);
lean_ctor_set(v___x_3304_, 8, v_initHeartbeats_3289_);
lean_ctor_set(v___x_3304_, 9, v_maxHeartbeats_3290_);
lean_ctor_set(v___x_3304_, 10, v_quotContext_3291_);
lean_ctor_set(v___x_3304_, 11, v_currMacroScope_3292_);
lean_ctor_set(v___x_3304_, 12, v_cancelTk_x3f_3294_);
lean_ctor_set(v___x_3304_, 13, v_inheritedTraceOptions_3296_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*14, v_diag_3293_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*14 + 1, v_suppressElabErrors_3295_);
v___x_3305_ = lean_unsigned_to_nat(128u);
v___x_3306_ = lean_nat_mod(v_visited_3301_, v___x_3305_);
lean_dec(v_visited_3301_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_nat_dec_eq(v___x_3306_, v___x_3307_);
lean_dec(v___x_3306_);
if (v___x_3308_ == 0)
{
v___y_3061_ = v___y_3298_;
v___y_3062_ = v_a_2376_;
v___y_3063_ = v_a_2377_;
v___y_3064_ = v_a_2378_;
v___y_3065_ = v_a_2379_;
v___y_3066_ = v_a_2380_;
v___y_3067_ = v___x_3304_;
v___y_3068_ = v_a_2382_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3310_ = l_Lean_Core_checkSystem(v___x_3309_, v___x_3304_, v_a_2382_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_dec_ref_known(v___x_3310_, 1);
v___y_3061_ = v___y_3298_;
v___y_3062_ = v_a_2376_;
v___y_3063_ = v_a_2377_;
v___y_3064_ = v_a_2378_;
v___y_3065_ = v_a_2379_;
v___y_3066_ = v_a_2380_;
v___y_3067_ = v___x_3304_;
v___y_3068_ = v_a_2382_;
goto v___jp_3060_;
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref_known(v___x_3304_, 14);
lean_dec_ref(v_code_2375_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v_inheritedTraceOptions_3296_);
lean_dec(v_cancelTk_x3f_3294_);
lean_dec(v_currMacroScope_3292_);
lean_dec(v_quotContext_3291_);
lean_dec(v_maxHeartbeats_3290_);
lean_dec(v_initHeartbeats_3289_);
lean_dec(v_openDecls_3288_);
lean_dec(v_currNamespace_3287_);
lean_dec(v_ref_3286_);
lean_dec(v_maxRecDepth_3285_);
lean_dec(v_currRecDepth_3284_);
lean_dec_ref(v_options_3283_);
lean_dec_ref(v_fileMap_3282_);
lean_dec_ref(v_fileName_3281_);
lean_dec_ref(v_code_2375_);
v_a_3319_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3299_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3299_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v___x_3327_; 
lean_dec_ref(v_code_2375_);
v___x_3327_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec_ref(v_a_2381_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_params_3341_; lean_object* v_type_3342_; lean_object* v_value_3343_; lean_object* v___x_3344_; lean_object* v_subst_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_params_3341_ = lean_ctor_get(v_decl_3332_, 2);
v_type_3342_ = lean_ctor_get(v_decl_3332_, 3);
v_value_3343_ = lean_ctor_get(v_decl_3332_, 4);
v___x_3344_ = lean_st_ref_get(v_a_3334_);
v_subst_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc_ref(v_subst_3345_);
lean_dec(v___x_3344_);
v___x_3346_ = 0;
v___x_3347_ = 0;
lean_inc_ref(v_type_3342_);
v___x_3348_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3346_, v_subst_3345_, v___x_3347_, v_type_3342_);
lean_dec_ref(v_subst_3345_);
lean_inc_ref(v_params_3341_);
v___x_3349_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3346_, v___x_3347_, v_params_3341_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
lean_inc_ref(v_a_3338_);
lean_inc_ref(v_value_3343_);
v___x_3351_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3343_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3346_, v_decl_3332_, v___x_3348_, v_a_3350_, v_a_3352_, v_a_3337_);
return v___x_3353_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_a_3350_);
lean_dec_ref(v___x_3348_);
lean_dec_ref(v_decl_3332_);
v_a_3354_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3351_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3351_);
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
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___x_3348_);
lean_dec_ref(v_decl_3332_);
v_a_3362_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3349_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3349_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3380_, lean_object* v___y_3381_, lean_object* v_i_3382_, lean_object* v_as_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
uint8_t v___y_47378__boxed_3392_; lean_object* v_res_3393_; 
v___y_47378__boxed_3392_ = lean_unbox(v___y_3381_);
v_res_3393_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3380_, v___y_47378__boxed_3392_, v_i_3382_, v_as_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3404_, lean_object* v_k_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3404_, v_k_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_);
lean_dec(v_a_3422_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3425_, uint8_t v_t_3426_, lean_object* v_decl_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3425_, v_t_3426_, v_decl_3427_, v___y_3429_, v___y_3432_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3437_, lean_object* v_t_3438_, lean_object* v_decl_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v_pu_boxed_3448_; uint8_t v_t_boxed_3449_; lean_object* v_res_3450_; 
v_pu_boxed_3448_ = lean_unbox(v_pu_3437_);
v_t_boxed_3449_ = lean_unbox(v_t_3438_);
v_res_3450_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3448_, v_t_boxed_3449_, v_decl_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3451_, uint8_t v_t_3452_, lean_object* v_args_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3451_, v_t_3452_, v_args_3453_, v___y_3455_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3463_, lean_object* v_t_3464_, lean_object* v_args_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
uint8_t v_pu_boxed_3474_; uint8_t v_t_boxed_3475_; lean_object* v_res_3476_; 
v_pu_boxed_3474_ = lean_unbox(v_pu_3463_);
v_t_boxed_3475_ = lean_unbox(v_t_3464_);
v_res_3476_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3474_, v_t_boxed_3475_, v_args_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3477_, lean_object* v_R_3478_, lean_object* v_a_3479_, lean_object* v_b_3480_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3479_, v_b_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3482_, lean_object* v_x_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3483_, v_x_3484_, v_x_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3487_, size_t v_i_3488_, size_t v_stop_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3487_, v_i_3488_, v_stop_3489_, v_b_3490_, v___y_3492_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3500_, lean_object* v_i_3501_, lean_object* v_stop_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
size_t v_i_boxed_3512_; size_t v_stop_boxed_3513_; lean_object* v_res_3514_; 
v_i_boxed_3512_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_stop_boxed_3513_ = lean_unbox_usize(v_stop_3502_);
lean_dec(v_stop_3502_);
v_res_3514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3500_, v_i_boxed_3512_, v_stop_boxed_3513_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_as_3500_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3515_, size_t v_i_3516_, size_t v_stop_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3515_, v_i_3516_, v_stop_3517_, v___y_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3527_, lean_object* v_i_3528_, lean_object* v_stop_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
size_t v_i_boxed_3538_; size_t v_stop_boxed_3539_; lean_object* v_res_3540_; 
v_i_boxed_3538_ = lean_unbox_usize(v_i_3528_);
lean_dec(v_i_3528_);
v_stop_boxed_3539_ = lean_unbox_usize(v_stop_3529_);
lean_dec(v_stop_3529_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3527_, v_i_boxed_3538_, v_stop_boxed_3539_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v_as_3527_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3541_, size_t v_i_3542_, size_t v_stop_3543_, lean_object* v_b_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3541_, v_i_3542_, v_stop_3543_, v_b_3544_, v___y_3546_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3551_, lean_object* v_i_3552_, lean_object* v_stop_3553_, lean_object* v_b_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
size_t v_i_boxed_3560_; size_t v_stop_boxed_3561_; lean_object* v_res_3562_; 
v_i_boxed_3560_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_stop_boxed_3561_ = lean_unbox_usize(v_stop_3553_);
lean_dec(v_stop_3553_);
v_res_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3551_, v_i_boxed_3560_, v_stop_boxed_3561_, v_b_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v_as_3551_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3563_, size_t v_i_3564_, size_t v_stop_3565_, lean_object* v_b_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3563_, v_i_3564_, v_stop_3565_, v_b_3566_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3576_, lean_object* v_i_3577_, lean_object* v_stop_3578_, lean_object* v_b_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_i_boxed_3588_; size_t v_stop_boxed_3589_; lean_object* v_res_3590_; 
v_i_boxed_3588_ = lean_unbox_usize(v_i_3577_);
lean_dec(v_i_3577_);
v_stop_boxed_3589_ = lean_unbox_usize(v_stop_3578_);
lean_dec(v_stop_3578_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3576_, v_i_boxed_3588_, v_stop_boxed_3589_, v_b_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v_as_3576_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3591_, size_t v_i_3592_, size_t v_stop_3593_, lean_object* v_b_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3591_, v_i_3592_, v_stop_3593_, v_b_3594_, v___y_3599_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3604_, lean_object* v_i_3605_, lean_object* v_stop_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
size_t v_i_boxed_3616_; size_t v_stop_boxed_3617_; lean_object* v_res_3618_; 
v_i_boxed_3616_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_stop_boxed_3617_ = lean_unbox_usize(v_stop_3606_);
lean_dec(v_stop_3606_);
v_res_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3604_, v_i_boxed_3616_, v_stop_boxed_3617_, v_b_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v_as_3604_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3619_, size_t v_i_3620_, size_t v_stop_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3619_, v_i_3620_, v_stop_3621_, v___y_3623_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3631_, lean_object* v_i_3632_, lean_object* v_stop_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
size_t v_i_boxed_3642_; size_t v_stop_boxed_3643_; lean_object* v_res_3644_; 
v_i_boxed_3642_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_stop_boxed_3643_ = lean_unbox_usize(v_stop_3633_);
lean_dec(v_stop_3633_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3631_, v_i_boxed_3642_, v_stop_boxed_3643_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v_as_3631_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3645_, size_t v_sz_3646_, size_t v_i_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3645_, v_sz_3646_, v_i_3647_, v_b_3648_, v___y_3650_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3658_, lean_object* v_sz_3659_, lean_object* v_i_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
size_t v_sz_boxed_3670_; size_t v_i_boxed_3671_; lean_object* v_res_3672_; 
v_sz_boxed_3670_ = lean_unbox_usize(v_sz_3659_);
lean_dec(v_sz_3659_);
v_i_boxed_3671_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_res_3672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3658_, v_sz_boxed_3670_, v_i_boxed_3671_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_as_3658_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3673_, lean_object* v_x_3674_, size_t v_x_3675_, size_t v_x_3676_, lean_object* v_x_3677_, lean_object* v_x_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3674_, v_x_3675_, v_x_3676_, v_x_3677_, v_x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
size_t v_x_51055__boxed_3686_; size_t v_x_51056__boxed_3687_; lean_object* v_res_3688_; 
v_x_51055__boxed_3686_ = lean_unbox_usize(v_x_3682_);
lean_dec(v_x_3682_);
v_x_51056__boxed_3687_ = lean_unbox_usize(v_x_3683_);
lean_dec(v_x_3683_);
v_res_3688_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3680_, v_x_3681_, v_x_51055__boxed_3686_, v_x_51056__boxed_3687_, v_x_3684_, v_x_3685_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3689_, uint8_t v_t_3690_, lean_object* v_i_3691_, lean_object* v_as_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3689_, v_t_3690_, v_i_3691_, v_as_3692_, v___y_3694_, v___y_3697_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3702_, lean_object* v_t_3703_, lean_object* v_i_3704_, lean_object* v_as_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
uint8_t v_pu_boxed_3714_; uint8_t v_t_boxed_3715_; lean_object* v_res_3716_; 
v_pu_boxed_3714_ = lean_unbox(v_pu_3702_);
v_t_boxed_3715_ = lean_unbox(v_t_3703_);
v_res_3716_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3714_, v_t_boxed_3715_, v_i_3704_, v_as_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3717_, lean_object* v_n_3718_, lean_object* v_k_3719_, lean_object* v_v_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3718_, v_k_3719_, v_v_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3722_, size_t v_depth_3723_, lean_object* v_keys_3724_, lean_object* v_vals_3725_, lean_object* v_heq_3726_, lean_object* v_i_3727_, lean_object* v_entries_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3723_, v_keys_3724_, v_vals_3725_, v_i_3727_, v_entries_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3730_, lean_object* v_depth_3731_, lean_object* v_keys_3732_, lean_object* v_vals_3733_, lean_object* v_heq_3734_, lean_object* v_i_3735_, lean_object* v_entries_3736_){
_start:
{
size_t v_depth_boxed_3737_; lean_object* v_res_3738_; 
v_depth_boxed_3737_ = lean_unbox_usize(v_depth_3731_);
lean_dec(v_depth_3731_);
v_res_3738_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3730_, v_depth_boxed_3737_, v_keys_3732_, v_vals_3733_, v_heq_3734_, v_i_3735_, v_entries_3736_);
lean_dec_ref(v_vals_3733_);
lean_dec_ref(v_keys_3732_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3739_, lean_object* v_x_3740_, lean_object* v_x_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3740_, v_x_3741_, v_x_3742_, v_x_3743_);
return v___x_3744_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
