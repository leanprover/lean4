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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
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
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_1_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* v_c_2_){
_start:
{
switch(lean_obj_tag(v_c_2_))
{
case 0:
{
lean_object* v_k_3_; 
v_k_3_ = lean_ctor_get(v_c_2_, 1);
v_c_2_ = v_k_3_;
goto _start;
}
case 1:
{
lean_object* v_k_5_; 
v_k_5_ = lean_ctor_get(v_c_2_, 1);
v_c_2_ = v_k_5_;
goto _start;
}
case 4:
{
lean_object* v_cases_7_; lean_object* v_alts_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_cases_7_ = lean_ctor_get(v_c_2_, 0);
v_alts_8_ = lean_ctor_get(v_cases_7_, 3);
v___x_9_ = lean_array_get_size(v_alts_8_);
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_dec_eq(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
return v___x_11_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_array_get_borrowed(v___x_12_, v_alts_8_, v___x_13_);
switch(lean_obj_tag(v___x_14_))
{
case 0:
{
lean_object* v_code_15_; 
v_code_15_ = lean_ctor_get(v___x_14_, 2);
v_c_2_ = v_code_15_;
goto _start;
}
case 1:
{
lean_object* v_code_17_; 
v_code_17_ = lean_ctor_get(v___x_14_, 1);
v_c_2_ = v_code_17_;
goto _start;
}
default: 
{
lean_object* v_code_19_; 
v_code_19_ = lean_ctor_get(v___x_14_, 0);
v_c_2_ = v_code_19_;
goto _start;
}
}
}
}
case 5:
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
default: 
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2_ = stack[0].m_obj;
uint8_t v_res_23_;
v_res_23_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_2_);
stack->m_num = v_res_23_;
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
uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* v_c_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_27_);
return v___x_28_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_27_ = stack[0].m_obj;
uint8_t v_res_29_;
v_res_29_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(v_c_27_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* v_c_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(v_c_30_);
lean_dec_ref(v_c_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* v_a_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 0;
return v___x_35_;
}
else
{
lean_object* v_key_36_; lean_object* v_tail_37_; uint8_t v___x_38_; 
v_key_36_ = lean_ctor_get(v_x_34_, 0);
v_tail_37_ = lean_ctor_get(v_x_34_, 2);
v___x_38_ = l_Lean_instBEqFVarId_beq(v_key_36_, v_a_33_);
if (v___x_38_ == 0)
{
v_x_34_ = v_tail_37_;
goto _start;
}
else
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_33_ = stack[0].m_obj;
lean_object* v_x_34_ = stack[1].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_33_, v_x_34_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* v_a_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_41_, v_x_42_);
lean_dec(v_x_42_);
lean_dec(v_a_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
return v_x_45_;
}
else
{
lean_object* v_key_47_; lean_object* v_value_48_; lean_object* v_tail_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_72_; 
v_key_47_ = lean_ctor_get(v_x_46_, 0);
v_value_48_ = lean_ctor_get(v_x_46_, 1);
v_tail_49_ = lean_ctor_get(v_x_46_, 2);
v_isSharedCheck_72_ = !lean_is_exclusive(v_x_46_);
if (v_isSharedCheck_72_ == 0)
{
v___x_51_ = v_x_46_;
v_isShared_52_ = v_isSharedCheck_72_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_tail_49_);
lean_inc(v_value_48_);
lean_inc(v_key_47_);
lean_dec(v_x_46_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_72_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v_fold_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_53_ = lean_array_get_size(v_x_45_);
v___x_54_ = l_Lean_instHashableFVarId_hash(v_key_47_);
v___x_55_ = 32ULL;
v___x_56_ = lean_uint64_shift_right(v___x_54_, v___x_55_);
v_fold_57_ = lean_uint64_xor(v___x_54_, v___x_56_);
v___x_58_ = 16ULL;
v___x_59_ = lean_uint64_shift_right(v_fold_57_, v___x_58_);
v___x_60_ = lean_uint64_xor(v_fold_57_, v___x_59_);
v___x_61_ = lean_uint64_to_usize(v___x_60_);
v___x_62_ = lean_usize_of_nat(v___x_53_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_sub(v___x_62_, v___x_63_);
v___x_65_ = lean_usize_land(v___x_61_, v___x_64_);
v___x_66_ = lean_array_uget_borrowed(v_x_45_, v___x_65_);
lean_inc(v___x_66_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 2, v___x_66_);
v___x_68_ = v___x_51_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_key_47_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_value_48_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v___x_66_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; 
v___x_69_ = lean_array_uset(v_x_45_, v___x_65_, v___x_68_);
v_x_45_ = v___x_69_;
v_x_46_ = v_tail_49_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object* v_i_73_, lean_object* v_source_74_, lean_object* v_target_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_array_get_size(v_source_74_);
v___x_77_ = lean_nat_dec_lt(v_i_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v_source_74_);
lean_dec(v_i_73_);
return v_target_75_;
}
else
{
lean_object* v_es_78_; lean_object* v___x_79_; lean_object* v_source_80_; lean_object* v_target_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_es_78_ = lean_array_fget(v_source_74_, v_i_73_);
v___x_79_ = lean_box(0);
v_source_80_ = lean_array_fset(v_source_74_, v_i_73_, v___x_79_);
v_target_81_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_target_75_, v_es_78_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_i_73_, v___x_82_);
lean_dec(v_i_73_);
v_i_73_ = v___x_83_;
v_source_74_ = v_source_80_;
v_target_75_ = v_target_81_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* v_data_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_nbuckets_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_86_ = lean_array_get_size(v_data_85_);
v___x_87_ = lean_unsigned_to_nat(2u);
v_nbuckets_88_ = lean_nat_mul(v___x_86_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_box(0);
v___x_91_ = lean_mk_array(v_nbuckets_88_, v___x_90_);
v___x_92_ = lean_array_propagate_mark(v_data_85_, v___x_91_);
v___x_93_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_89_, v_data_85_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object* v_a_94_, lean_object* v_b_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_dec(v_b_95_);
lean_dec(v_a_94_);
return v_x_96_;
}
else
{
lean_object* v_key_97_; lean_object* v_value_98_; lean_object* v_tail_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
v_key_97_ = lean_ctor_get(v_x_96_, 0);
v_value_98_ = lean_ctor_get(v_x_96_, 1);
v_tail_99_ = lean_ctor_get(v_x_96_, 2);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_111_ == 0)
{
v___x_101_ = v_x_96_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_tail_99_);
lean_inc(v_value_98_);
lean_inc(v_key_97_);
lean_dec(v_x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_instBEqFVarId_beq(v_key_97_, v_a_94_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_94_, v_b_95_, v_tail_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 2, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_key_97_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_value_98_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec(v_value_98_);
lean_dec(v_key_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_b_95_);
lean_ctor_set(v___x_101_, 0, v_a_94_);
v___x_109_ = v___x_101_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_94_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_b_95_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_tail_99_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* v_m_112_, lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
lean_object* v_size_115_; lean_object* v_buckets_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_159_; 
v_size_115_ = lean_ctor_get(v_m_112_, 0);
v_buckets_116_ = lean_ctor_get(v_m_112_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_m_112_);
if (v_isSharedCheck_159_ == 0)
{
v___x_118_ = v_m_112_;
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_buckets_116_);
lean_inc(v_size_115_);
lean_dec(v_m_112_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v_fold_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v_bkt_133_; uint8_t v___x_134_; 
v___x_120_ = lean_array_get_size(v_buckets_116_);
v___x_121_ = l_Lean_instHashableFVarId_hash(v_a_113_);
v___x_122_ = 32ULL;
v___x_123_ = lean_uint64_shift_right(v___x_121_, v___x_122_);
v_fold_124_ = lean_uint64_xor(v___x_121_, v___x_123_);
v___x_125_ = 16ULL;
v___x_126_ = lean_uint64_shift_right(v_fold_124_, v___x_125_);
v___x_127_ = lean_uint64_xor(v_fold_124_, v___x_126_);
v___x_128_ = lean_uint64_to_usize(v___x_127_);
v___x_129_ = lean_usize_of_nat(v___x_120_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_usize_land(v___x_128_, v___x_131_);
v_bkt_133_ = lean_array_uget_borrowed(v_buckets_116_, v___x_132_);
v___x_134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_113_, v_bkt_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v_size_x27_136_; lean_object* v___x_137_; lean_object* v_buckets_x27_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v_size_x27_136_ = lean_nat_add(v_size_115_, v___x_135_);
lean_dec(v_size_115_);
lean_inc(v_bkt_133_);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v_a_113_);
lean_ctor_set(v___x_137_, 1, v_b_114_);
lean_ctor_set(v___x_137_, 2, v_bkt_133_);
v_buckets_x27_138_ = lean_array_uset(v_buckets_116_, v___x_132_, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(4u);
v___x_140_ = lean_nat_mul(v_size_x27_136_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(3u);
v___x_142_ = lean_nat_div(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_array_get_size(v_buckets_x27_138_);
v___x_144_ = lean_nat_dec_le(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
if (v___x_144_ == 0)
{
lean_object* v_val_145_; lean_object* v___x_147_; 
v_val_145_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_buckets_x27_138_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_val_145_);
lean_ctor_set(v___x_118_, 0, v_size_x27_136_);
v___x_147_ = v___x_118_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_size_x27_136_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_val_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
else
{
lean_object* v___x_150_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_buckets_x27_138_);
lean_ctor_set(v___x_118_, 0, v_size_x27_136_);
v___x_150_ = v___x_118_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_size_x27_136_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_buckets_x27_138_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
lean_object* v___x_152_; lean_object* v_buckets_x27_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_inc(v_bkt_133_);
v___x_152_ = lean_box(0);
v_buckets_x27_153_ = lean_array_uset(v_buckets_116_, v___x_132_, v___x_152_);
v___x_154_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_113_, v_b_114_, v_bkt_133_);
v___x_155_ = lean_array_uset(v_buckets_x27_153_, v___x_132_, v___x_154_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_155_);
v___x_157_ = v___x_118_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_115_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* v_as_160_, size_t v_sz_161_, size_t v_i_162_, lean_object* v_b_163_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_b_163_);
return v___x_166_;
}
else
{
lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_202_; 
v_snd_167_ = lean_ctor_get(v_b_163_, 1);
v_fst_168_ = lean_ctor_get(v_b_163_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_b_163_);
if (v_isSharedCheck_202_ == 0)
{
v___x_170_ = v_b_163_;
v_isShared_171_ = v_isSharedCheck_202_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_snd_167_);
lean_inc(v_fst_168_);
lean_dec(v_b_163_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_202_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_array_172_; lean_object* v_start_173_; lean_object* v_stop_174_; uint8_t v___x_175_; 
v_array_172_ = lean_ctor_get(v_snd_167_, 0);
v_start_173_ = lean_ctor_get(v_snd_167_, 1);
v_stop_174_ = lean_ctor_get(v_snd_167_, 2);
v___x_175_ = lean_nat_dec_lt(v_start_173_, v_stop_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_177_; 
if (v_isShared_171_ == 0)
{
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_fst_168_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_snd_167_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
else
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_198_; 
lean_inc(v_stop_174_);
lean_inc(v_start_173_);
lean_inc_ref(v_array_172_);
v_isSharedCheck_198_ = !lean_is_exclusive(v_snd_167_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; 
v_unused_199_ = lean_ctor_get(v_snd_167_, 2);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_snd_167_, 1);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_snd_167_, 0);
lean_dec(v_unused_201_);
v___x_181_ = v_snd_167_;
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_snd_167_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_198_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_a_183_; lean_object* v_fvarId_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v_a_183_ = lean_array_uget_borrowed(v_as_160_, v_i_162_);
v_fvarId_184_ = lean_ctor_get(v_a_183_, 0);
v___x_185_ = lean_array_fget(v_array_172_, v_start_173_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_start_173_, v___x_186_);
lean_dec(v_start_173_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_187_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_array_172_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_stop_174_);
v___x_189_ = v_reuseFailAlloc_197_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc(v_fvarId_184_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_168_, v_fvarId_184_, v___x_185_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_189_);
lean_ctor_set(v___x_170_, 0, v___x_190_);
v___x_192_ = v___x_170_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_189_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_162_, v___x_193_);
v_i_162_ = v___x_194_;
v_b_163_ = v___x_192_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_160_ = stack[0].m_obj;
size_t v_sz_161_ = stack[1].m_num;
size_t v_i_162_ = stack[2].m_num;
lean_object* v_b_163_ = stack[3].m_obj;
lean_object* v_res_203_;
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_160_, v_sz_161_, v_i_162_, v_b_163_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* v_as_204_, lean_object* v_sz_205_, lean_object* v_i_206_, lean_object* v_b_207_, lean_object* v___y_208_){
_start:
{
size_t v_sz_boxed_209_; size_t v_i_boxed_210_; lean_object* v_res_211_; 
v_sz_boxed_209_ = lean_unbox_usize(v_sz_205_);
lean_dec(v_sz_205_);
v_i_boxed_210_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_204_, v_sz_boxed_209_, v_i_boxed_210_, v_b_207_);
lean_dec_ref(v_as_204_);
return v_res_211_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* v_a_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_array_219_; lean_object* v_start_220_; lean_object* v_stop_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_271_; 
v_array_219_ = lean_ctor_get(v_a_212_, 0);
v_start_220_ = lean_ctor_get(v_a_212_, 1);
v_stop_221_ = lean_ctor_get(v_a_212_, 2);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_271_ == 0)
{
v___x_223_ = v_a_212_;
v_isShared_224_ = v_isSharedCheck_271_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_stop_221_);
lean_inc(v_start_220_);
lean_inc(v_array_219_);
lean_dec(v_a_212_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_271_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_lt(v_start_220_, v_stop_221_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_del_object(v___x_223_);
lean_dec(v_stop_221_);
lean_dec(v_start_220_);
lean_dec_ref(v_array_219_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_b_213_);
return v___x_226_;
}
else
{
lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_270_; 
v_fst_227_ = lean_ctor_get(v_b_213_, 0);
v_snd_228_ = lean_ctor_get(v_b_213_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_b_213_);
if (v_isSharedCheck_270_ == 0)
{
v___x_230_ = v_b_213_;
v_isShared_231_ = v_isSharedCheck_270_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_b_213_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_270_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_fvarId_233_; lean_object* v_type_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_232_ = lean_array_fget_borrowed(v_array_219_, v_start_220_);
v_fvarId_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_fvarId_233_);
v_type_234_ = lean_ctor_get(v___x_232_, 2);
lean_inc_ref(v_type_234_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_start_220_, v___x_235_);
lean_dec(v_start_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_236_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_array_219_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_stop_221_);
v___x_238_ = v_reuseFailAlloc_269_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_239_ = 0;
v___x_240_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v___x_239_, v_type_234_, v_fst_227_, v___x_225_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = 0;
v___x_243_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_239_, v_a_241_, v___x_242_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v_fvarId_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v_fvarId_245_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_fvarId_245_);
v___x_246_ = lean_array_push(v_snd_228_, v_a_244_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_fvarId_245_);
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_227_, v_fvarId_233_, v___x_247_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_246_);
lean_ctor_set(v___x_230_, 0, v___x_248_);
v___x_250_ = v___x_230_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_246_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v_a_212_ = v___x_238_;
v_b_213_ = v___x_250_;
goto _start;
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v___x_238_);
lean_dec(v_fvarId_233_);
lean_del_object(v___x_230_);
lean_dec(v_snd_228_);
lean_dec(v_fst_227_);
v_a_253_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_243_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v___x_238_);
lean_dec(v_fvarId_233_);
lean_del_object(v___x_230_);
lean_dec(v_snd_228_);
lean_dec(v_fst_227_);
v_a_261_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_240_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_240_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_212_ = stack[0].m_obj;
lean_object* v_b_213_ = stack[1].m_obj;
lean_object* v___y_214_ = stack[2].m_obj;
lean_object* v___y_215_ = stack[3].m_obj;
lean_object* v___y_216_ = stack[4].m_obj;
lean_object* v___y_217_ = stack[5].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_212_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* v_a_273_, lean_object* v_b_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_273_, v_b_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_box(0);
v___x_282_ = lean_unsigned_to_nat(16u);
v___x_283_ = lean_mk_array(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_subst_286_; 
v___x_284_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
v___x_285_ = lean_unsigned_to_nat(0u);
v_subst_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_subst_286_, 0, v___x_285_);
lean_ctor_set(v_subst_286_, 1, v___x_284_);
return v_subst_286_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* v_info_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_params_301_; lean_object* v_value_302_; lean_object* v_args_303_; lean_object* v___x_304_; lean_object* v_subst_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; size_t v_sz_309_; size_t v___x_310_; lean_object* v___x_311_; 
v_params_301_ = lean_ctor_get(v_info_292_, 0);
lean_inc_ref(v_params_301_);
v_value_302_ = lean_ctor_get(v_info_292_, 1);
lean_inc_ref(v_value_302_);
v_args_303_ = lean_ctor_get(v_info_292_, 3);
lean_inc_ref(v_args_303_);
lean_dec_ref(v_info_292_);
v___x_304_ = lean_unsigned_to_nat(0u);
v_subst_305_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
v___x_306_ = lean_array_get_size(v_args_303_);
v___x_307_ = l_Array_toSubarray___redArg(v_args_303_, v___x_304_, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_subst_305_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v_sz_309_ = lean_array_size(v_params_301_);
v___x_310_ = ((size_t)0ULL);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_params_301_, v_sz_309_, v___x_310_, v___x_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_fst_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_362_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v_fst_313_ = lean_ctor_get(v_a_312_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_a_312_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_a_312_, 1);
lean_dec(v_unused_363_);
v___x_315_ = v_a_312_;
v_isShared_316_ = v_isSharedCheck_362_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_fst_313_);
lean_dec(v_a_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_362_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v_lower_319_; lean_object* v_upper_320_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_317_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2));
v___x_360_ = lean_array_get_size(v_params_301_);
v___x_361_ = lean_nat_dec_le(v___x_306_, v___x_304_);
if (v___x_361_ == 0)
{
v_lower_319_ = v___x_306_;
v_upper_320_ = v___x_360_;
goto v___jp_318_;
}
else
{
v_lower_319_ = v___x_304_;
v_upper_320_ = v___x_360_;
goto v___jp_318_;
}
v___jp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = l_Array_toSubarray___redArg(v_params_301_, v_lower_319_, v_upper_320_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_317_);
v___x_323_ = v___x_315_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_317_);
v___x_323_ = v_reuseFailAlloc_359_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; 
v___x_324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v___x_321_, v___x_323_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; uint8_t v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v_fst_326_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_326_);
v_snd_327_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_snd_327_);
lean_dec(v_a_325_);
v___x_328_ = 0;
v___x_329_ = 0;
v___x_330_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_328_, v_value_302_, v_fst_326_, v___x_329_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_n(v_a_331_, 2);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_331_, v___x_329_, v_a_294_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec_ref_known(v___x_332_, 1);
v___x_333_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_334_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_snd_327_, v_a_331_, v___x_333_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
return v___x_334_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_a_331_);
lean_dec(v_snd_327_);
v_a_335_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_332_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_332_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_snd_327_);
v_a_343_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_330_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_330_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_value_302_);
v_a_351_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_324_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_324_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_value_302_);
lean_dec_ref(v_params_301_);
v_a_364_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_311_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_311_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_specializePartialApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_292_ = stack[0].m_obj;
lean_object* v_a_293_ = stack[1].m_obj;
lean_object* v_a_294_ = stack[2].m_obj;
lean_object* v_a_295_ = stack[3].m_obj;
lean_object* v_a_296_ = stack[4].m_obj;
lean_object* v_a_297_ = stack[5].m_obj;
lean_object* v_a_298_ = stack[6].m_obj;
lean_object* v_a_299_ = stack[7].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_info_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* v_info_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_info_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_384_, v_a_385_, v_b_386_);
return v___x_387_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* v_as_388_, size_t v_sz_389_, size_t v_i_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_388_, v_sz_389_, v_i_390_, v_b_391_);
return v___x_400_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_388_ = stack[0].m_obj;
size_t v_sz_389_ = stack[1].m_num;
size_t v_i_390_ = stack[2].m_num;
lean_object* v_b_391_ = stack[3].m_obj;
lean_object* v___y_392_ = stack[4].m_obj;
lean_object* v___y_393_ = stack[5].m_obj;
lean_object* v___y_394_ = stack[6].m_obj;
lean_object* v___y_395_ = stack[7].m_obj;
lean_object* v___y_396_ = stack[8].m_obj;
lean_object* v___y_397_ = stack[9].m_obj;
lean_object* v___y_398_ = stack[10].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_388_, v_sz_389_, v_i_390_, v_b_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* v_as_402_, lean_object* v_sz_403_, lean_object* v_i_404_, lean_object* v_b_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
size_t v_sz_boxed_414_; size_t v_i_boxed_415_; lean_object* v_res_416_; 
v_sz_boxed_414_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_i_boxed_415_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_402_, v_sz_boxed_414_, v_i_boxed_415_, v_b_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec_ref(v_as_402_);
return v_res_416_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* v_inst_417_, lean_object* v_R_418_, lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v_c_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_419_, v_b_420_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_419_ = stack[2].m_obj;
lean_object* v_b_420_ = stack[3].m_obj;
lean_object* v___y_422_ = stack[5].m_obj;
lean_object* v___y_423_ = stack[6].m_obj;
lean_object* v___y_424_ = stack[7].m_obj;
lean_object* v___y_425_ = stack[8].m_obj;
lean_object* v___y_426_ = stack[9].m_obj;
lean_object* v___y_427_ = stack[10].m_obj;
lean_object* v___y_428_ = stack[11].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_box(0), lean_box(0), v_a_419_, v_b_420_, lean_box(0), v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* v_inst_432_, lean_object* v_R_433_, lean_object* v_a_434_, lean_object* v_b_435_, lean_object* v_c_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(v_inst_432_, v_R_433_, v_a_434_, v_b_435_, v_c_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_445_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_447_ = stack[1].m_obj;
lean_object* v_x_448_ = stack[2].m_obj;
uint8_t v_res_450_;
v_res_450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_box(0), v_a_447_, v_x_448_);
stack->m_num = v_res_450_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* v_00_u03b2_451_, lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_451_, v_a_452_, v_x_453_);
lean_dec(v_x_453_);
lean_dec(v_a_452_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* v_00_u03b2_456_, lean_object* v_data_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_data_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_460_, v_b_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_464_, lean_object* v_i_465_, lean_object* v_source_466_, lean_object* v_target_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v_i_465_, v_source_466_, v_target_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_x_470_, v_x_471_);
return v___x_472_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* v_fvarId_473_, lean_object* v_args_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___x_483_; lean_object* v___x_484_; 
v___x_483_ = 0;
v___x_484_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_483_, v_fvarId_473_, v_a_479_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_549_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_549_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_549_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_549_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
if (lean_obj_tag(v_a_485_) == 1)
{
lean_object* v_val_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_544_; 
lean_del_object(v___x_487_);
v_val_489_ = lean_ctor_get(v_a_485_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_544_ == 0)
{
v___x_491_ = v_a_485_;
v_isShared_492_ = v_isSharedCheck_544_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_val_489_);
lean_dec(v_a_485_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_544_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_val_489_, v_a_476_, v_a_478_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_535_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_535_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_535_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_535_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; 
v___x_498_ = lean_unbox(v_a_494_);
lean_dec(v_a_494_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_501_; 
lean_del_object(v___x_491_);
lean_dec(v_val_489_);
lean_dec_ref(v_args_474_);
v___x_499_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_object* v___x_503_; 
lean_del_object(v___x_496_);
v___x_503_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_476_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_params_504_; lean_object* v_value_505_; uint8_t v___x_506_; lean_object* v___x_507_; 
lean_dec_ref_known(v___x_503_, 1);
v_params_504_ = lean_ctor_get(v_val_489_, 2);
lean_inc_ref(v_params_504_);
v_value_505_ = lean_ctor_get(v_val_489_, 4);
lean_inc_ref(v_value_505_);
lean_dec(v_val_489_);
v___x_506_ = 0;
v___x_507_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_504_, v_value_505_, v_args_474_, v___x_506_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec_ref(v_params_504_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_a_508_);
v___x_513_ = v___x_491_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
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
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_491_);
v_a_519_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_507_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_507_);
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
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_491_);
lean_dec(v_val_489_);
lean_dec_ref(v_args_474_);
v_a_527_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_503_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_503_);
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
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_del_object(v___x_491_);
lean_dec(v_val_489_);
lean_dec_ref(v_args_474_);
v_a_536_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_493_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_493_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_547_; 
lean_dec(v_a_485_);
lean_dec_ref(v_args_474_);
v___x_545_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_545_);
v___x_547_ = v___x_487_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
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
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v_args_474_);
v_a_550_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_484_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_484_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineJp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_473_ = stack[0].m_obj;
lean_object* v_args_474_ = stack[1].m_obj;
lean_object* v_a_475_ = stack[2].m_obj;
lean_object* v_a_476_ = stack[3].m_obj;
lean_object* v_a_477_ = stack[4].m_obj;
lean_object* v_a_478_ = stack[5].m_obj;
lean_object* v_a_479_ = stack[6].m_obj;
lean_object* v_a_480_ = stack[7].m_obj;
lean_object* v_a_481_ = stack[8].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_473_, v_args_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* v_fvarId_559_, lean_object* v_args_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_559_, v_args_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_fvarId_559_);
return v_res_569_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* v_declName_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_env_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_573_);
v___x_575_ = l_Lean_isInstanceReducibleCore(v_env_574_, v_declName_570_);
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_570_ = stack[0].m_obj;
lean_object* v___y_571_ = stack[1].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_570_, v___y_571_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_580_, v___y_581_);
lean_dec(v___y_581_);
return v_res_583_;
}
}
lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* v_declName_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_584_, v___y_591_);
return v___x_593_;
}
}
LEAN_EXPORT void l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_584_ = stack[0].m_obj;
lean_object* v___y_585_ = stack[1].m_obj;
lean_object* v___y_586_ = stack[2].m_obj;
lean_object* v___y_587_ = stack[3].m_obj;
lean_object* v___y_588_ = stack[4].m_obj;
lean_object* v___y_589_ = stack[5].m_obj;
lean_object* v___y_590_ = stack[6].m_obj;
lean_object* v___y_591_ = stack[7].m_obj;
lean_object* v_res_594_;
v_res_594_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* v_declName_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_604_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t v_sz_605_, size_t v_i_606_, lean_object* v_bs_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_608_ == 0)
{
return v_bs_607_;
}
else
{
lean_object* v_v_609_; lean_object* v_fvarId_610_; lean_object* v___x_611_; lean_object* v_bs_x27_612_; lean_object* v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v_v_609_ = lean_array_uget_borrowed(v_bs_607_, v_i_606_);
v_fvarId_610_ = lean_ctor_get(v_v_609_, 0);
lean_inc(v_fvarId_610_);
v___x_611_ = lean_unsigned_to_nat(0u);
v_bs_x27_612_ = lean_array_uset(v_bs_607_, v_i_606_, v___x_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_fvarId_610_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_606_, v___x_614_);
v___x_616_ = lean_array_uset(v_bs_x27_612_, v_i_606_, v___x_613_);
v_i_606_ = v___x_615_;
v_bs_607_ = v___x_616_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_605_ = stack[0].m_num;
size_t v_i_606_ = stack[1].m_num;
lean_object* v_bs_607_ = stack[2].m_obj;
lean_object* v_res_618_;
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_605_, v_i_606_, v_bs_607_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object* v_sz_619_, lean_object* v_i_620_, lean_object* v_bs_621_){
_start:
{
size_t v_sz_boxed_622_; size_t v_i_boxed_623_; lean_object* v_res_624_; 
v_sz_boxed_622_ = lean_unbox_usize(v_sz_619_);
lean_dec(v_sz_619_);
v_i_boxed_623_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_622_, v_i_boxed_623_, v_bs_621_);
return v_res_624_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* v_letDecl_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_config_640_; uint8_t v_etaPoly_641_; 
v_config_640_ = lean_ctor_get(v_a_629_, 1);
v_etaPoly_641_ = lean_ctor_get_uint8(v_config_640_, 0);
if (v_etaPoly_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_letDecl_628_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v_value_644_; 
v_value_644_ = lean_ctor_get(v_letDecl_628_, 3);
lean_inc(v_value_644_);
if (lean_obj_tag(v_value_644_) == 3)
{
lean_object* v_fvarId_645_; lean_object* v_type_646_; lean_object* v_declName_647_; lean_object* v_us_648_; lean_object* v_args_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_809_; 
v_fvarId_645_ = lean_ctor_get(v_letDecl_628_, 0);
v_type_646_ = lean_ctor_get(v_letDecl_628_, 2);
v_declName_647_ = lean_ctor_get(v_value_644_, 0);
v_us_648_ = lean_ctor_get(v_value_644_, 1);
v_args_649_ = lean_ctor_get(v_value_644_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_value_644_);
if (v_isSharedCheck_809_ == 0)
{
v___x_651_ = v_value_644_;
v_isShared_652_ = v_isSharedCheck_809_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_args_649_);
lean_inc(v_us_648_);
lean_inc(v_declName_647_);
lean_dec(v_value_644_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_809_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v_env_654_; uint8_t v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_st_ref_get(v_a_635_);
v_env_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_env_654_);
lean_dec(v___x_653_);
v___x_655_ = 0;
lean_inc(v_declName_647_);
v___x_656_ = l_Lean_Environment_find_x3f(v_env_654_, v_declName_647_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 1)
{
lean_object* v_val_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_val_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_ConstantInfo_type(v_val_657_);
lean_dec(v_val_657_);
v___x_659_ = l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_658_, v_a_635_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_798_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_798_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_798_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_798_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
uint8_t v___x_664_; 
v___x_664_ = lean_unbox(v_a_660_);
lean_dec(v_a_660_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v___x_665_ = lean_box(0);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_797_; 
lean_del_object(v___x_662_);
lean_inc(v_declName_647_);
v___x_669_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_647_, v_a_635_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_797_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_797_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_797_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_796_; 
v_val_674_ = lean_ctor_get(v_a_670_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_796_ == 0)
{
v___x_676_ = v_a_670_;
v_isShared_677_ = v_isSharedCheck_796_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v_a_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_796_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
uint8_t v___x_678_; 
v___x_678_ = lean_unbox(v_val_674_);
lean_dec(v_val_674_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_del_object(v___x_672_);
v___x_679_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_632_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; uint8_t v___x_681_; lean_object* v___x_682_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = lean_unbox(v_a_680_);
lean_inc(v_declName_647_);
v___x_682_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_647_, v___x_681_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_775_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_775_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_775_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_775_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
if (lean_obj_tag(v_a_683_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_774_; 
v_val_687_ = lean_ctor_get(v_a_683_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_774_ == 0)
{
v___x_689_ = v_a_683_;
v_isShared_690_ = v_isSharedCheck_774_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_val_687_);
lean_dec(v_a_683_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_774_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___x_692_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = lean_array_get_size(v_args_649_);
v___x_694_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_687_);
lean_dec(v_val_687_);
v___x_695_ = lean_nat_dec_lt(v___x_693_, v___x_694_);
lean_dec(v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_del_object(v___x_689_);
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v___x_696_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_696_);
v___x_698_ = v___x_685_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_700_; 
lean_del_object(v___x_685_);
lean_inc_ref(v_type_646_);
v___x_700_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_692_, v_type_646_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; size_t v_sz_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc_n(v_a_701_, 2);
lean_dec_ref_known(v___x_700_, 1);
v_sz_702_ = lean_array_size(v_a_701_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_702_, v___x_703_, v_a_701_);
v___x_705_ = l_Array_append___redArg(v_args_649_, v___x_704_);
lean_dec_ref(v___x_704_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v___x_705_);
v___x_707_ = v___x_651_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_declName_647_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_us_648_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v___x_705_);
v___x_707_ = v_reuseFailAlloc_765_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_709_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_692_, v___x_707_, v___x_708_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_fvarId_711_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_fvarId_711_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_fvarId_711_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 5);
lean_ctor_set(v___x_676_, 0, v_fvarId_711_);
v___x_713_ = v___x_676_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fvarId_711_);
v___x_713_ = v_reuseFailAlloc_756_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_a_710_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_716_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_701_, v___x_714_, v___x_715_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_fvarId_718_; lean_object* v___x_720_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v_fvarId_718_ = lean_ctor_get(v_a_717_, 0);
lean_inc(v_fvarId_718_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v_a_717_);
v___x_720_ = v___x_689_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_717_);
v___x_720_ = v_reuseFailAlloc_747_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; 
lean_inc(v_fvarId_645_);
v___x_721_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_645_, v_fvarId_718_, v_a_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
lean_dec_ref_known(v___x_721_, 1);
v___x_722_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_628_, v_a_630_, v_a_633_);
lean_dec_ref(v_letDecl_628_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_730_);
v___x_724_ = v___x_722_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_720_);
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_720_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_720_);
v_a_731_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_722_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_722_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___x_720_);
lean_dec_ref(v_letDecl_628_);
v_a_739_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_721_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_721_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_del_object(v___x_689_);
lean_dec_ref(v_letDecl_628_);
v_a_748_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_716_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_716_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_701_);
lean_del_object(v___x_689_);
lean_del_object(v___x_676_);
lean_dec_ref(v_letDecl_628_);
v_a_757_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_709_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_709_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_689_);
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v_a_766_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_700_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_700_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
lean_del_object(v___x_689_);
lean_dec(v_val_687_);
lean_del_object(v___x_685_);
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
goto v___jp_637_;
}
}
}
else
{
lean_del_object(v___x_685_);
lean_dec(v_a_683_);
lean_dec(v_a_680_);
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
goto v___jp_637_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_680_);
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v_a_776_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_682_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_682_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v_a_784_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_679_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_679_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v___x_792_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_792_);
v___x_794_ = v___x_672_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v_a_799_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_659_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_659_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_656_);
lean_del_object(v___x_651_);
lean_dec_ref(v_args_649_);
lean_dec(v_us_648_);
lean_dec(v_declName_647_);
lean_dec_ref(v_letDecl_628_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_value_644_);
lean_dec_ref(v_letDecl_628_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
v___jp_637_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_letDecl_628_ = stack[0].m_obj;
lean_object* v_a_629_ = stack[1].m_obj;
lean_object* v_a_630_ = stack[2].m_obj;
lean_object* v_a_631_ = stack[3].m_obj;
lean_object* v_a_632_ = stack[4].m_obj;
lean_object* v_a_633_ = stack[5].m_obj;
lean_object* v_a_634_ = stack[6].m_obj;
lean_object* v_a_635_ = stack[7].m_obj;
lean_object* v_res_812_;
v_res_812_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* v_letDecl_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_822_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t v___x_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_bs_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_824_, v_i_825_, v_bs_826_);
return v___x_827_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_823_ = stack[0].m_num;
size_t v_sz_824_ = stack[1].m_num;
size_t v_i_825_ = stack[2].m_num;
lean_object* v_bs_826_ = stack[3].m_obj;
lean_object* v_res_828_;
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_823_, v_sz_824_, v_i_825_, v_bs_826_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* v___x_829_, lean_object* v_sz_830_, lean_object* v_i_831_, lean_object* v_bs_832_){
_start:
{
uint8_t v___x_23277__boxed_833_; size_t v_sz_boxed_834_; size_t v_i_boxed_835_; lean_object* v_res_836_; 
v___x_23277__boxed_833_ = lean_unbox(v___x_829_);
v_sz_boxed_834_ = lean_unbox_usize(v_sz_830_);
lean_dec(v_sz_830_);
v_i_boxed_835_ = lean_unbox_usize(v_i_831_);
lean_dec(v_i_831_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_23277__boxed_833_, v_sz_boxed_834_, v_i_boxed_835_, v_bs_832_);
return v_res_836_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* v_c_837_, lean_object* v_fvarId_838_, lean_object* v_a_839_){
_start:
{
if (lean_obj_tag(v_c_837_) == 5)
{
lean_object* v_fvarId_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_863_; 
v_fvarId_841_ = lean_ctor_get(v_c_837_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_c_837_);
if (v_isSharedCheck_863_ == 0)
{
v___x_843_ = v_c_837_;
v_isShared_844_ = v_isSharedCheck_863_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_fvarId_841_);
lean_dec(v_c_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_863_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v_subst_847_; lean_object* v___x_848_; 
v___x_845_ = 0;
v___x_846_ = lean_st_ref_get(v_a_839_);
v_subst_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc_ref(v_subst_847_);
lean_dec(v___x_846_);
v___x_848_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_847_, v_fvarId_841_, v___x_845_);
lean_dec_ref(v_subst_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_fvarId_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_843_);
v_fvarId_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_fvarId_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = l_Lean_instBEqFVarId_beq(v_fvarId_849_, v_fvarId_838_);
lean_dec(v_fvarId_849_);
v___x_854_ = lean_box(v___x_853_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_box(v___x_845_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_859_);
v___x_861_ = v___x_843_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_c_837_);
v___x_864_ = 0;
v___x_865_ = lean_box(v___x_864_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_837_ = stack[0].m_obj;
lean_object* v_fvarId_838_ = stack[1].m_obj;
lean_object* v_a_839_ = stack[2].m_obj;
lean_object* v_res_867_;
v_res_867_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_837_, v_fvarId_838_, v_a_839_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* v_c_868_, lean_object* v_fvarId_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_868_, v_fvarId_869_, v_a_870_);
lean_dec(v_a_870_);
lean_dec(v_fvarId_869_);
return v_res_872_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* v_c_873_, lean_object* v_fvarId_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_873_, v_fvarId_874_, v_a_876_);
return v___x_883_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isReturnOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_873_ = stack[0].m_obj;
lean_object* v_fvarId_874_ = stack[1].m_obj;
lean_object* v_a_875_ = stack[2].m_obj;
lean_object* v_a_876_ = stack[3].m_obj;
lean_object* v_a_877_ = stack[4].m_obj;
lean_object* v_a_878_ = stack[5].m_obj;
lean_object* v_a_879_ = stack[6].m_obj;
lean_object* v_a_880_ = stack[7].m_obj;
lean_object* v_a_881_ = stack[8].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_873_, v_fvarId_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* v_c_885_, lean_object* v_fvarId_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_885_, v_fvarId_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_fvarId_886_);
return v_res_895_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* v_value_896_){
_start:
{
if (lean_obj_tag(v_value_896_) == 4)
{
lean_object* v_fvarId_901_; lean_object* v_args_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_fvarId_901_ = lean_ctor_get(v_value_896_, 0);
v_args_902_ = lean_ctor_get(v_value_896_, 1);
v___x_903_ = lean_array_get_size(v_args_902_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_nat_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
goto v___jp_898_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc(v_fvarId_901_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_fvarId_901_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
else
{
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_box(0);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_896_ = stack[0].m_obj;
lean_object* v_res_908_;
v_res_908_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_896_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* v_value_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_909_);
lean_dec(v_value_909_);
return v_res_911_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* v_value_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_912_);
return v___x_921_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_elimVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_912_ = stack[0].m_obj;
lean_object* v_a_913_ = stack[1].m_obj;
lean_object* v_a_914_ = stack[2].m_obj;
lean_object* v_a_915_ = stack[3].m_obj;
lean_object* v_a_916_ = stack[4].m_obj;
lean_object* v_a_917_ = stack[5].m_obj;
lean_object* v_a_918_ = stack[6].m_obj;
lean_object* v_a_919_ = stack[7].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* v_value_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_value_923_);
return v_res_932_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* v_a_933_, lean_object* v___x_934_, lean_object* v_fvarId_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_fvarId_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_fvarId_941_ = lean_ctor_get(v_a_933_, 0);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_fvarId_935_);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_934_);
v___x_944_ = lean_array_push(v___x_943_, v___x_942_);
lean_inc(v_fvarId_941_);
v___x_945_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_945_, 0, v_fvarId_941_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_933_ = stack[0].m_obj;
lean_object* v___x_934_ = stack[1].m_obj;
lean_object* v_fvarId_935_ = stack[2].m_obj;
lean_object* v___y_936_ = stack[3].m_obj;
lean_object* v___y_937_ = stack[4].m_obj;
lean_object* v___y_938_ = stack[5].m_obj;
lean_object* v___y_939_ = stack[6].m_obj;
lean_object* v_res_947_;
v_res_947_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_933_, v___x_934_, v_fvarId_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* v_a_948_, lean_object* v___x_949_, lean_object* v_fvarId_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_948_, v___x_949_, v_fvarId_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___x_949_);
lean_dec_ref(v_a_948_);
return v_res_956_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t v_pu_957_, uint8_t v_t_958_, lean_object* v_args_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_subst_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = lean_st_ref_get(v___y_960_);
v_subst_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_subst_963_);
lean_dec(v___x_962_);
v___x_964_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_957_, v_subst_963_, v_args_959_, v_t_958_);
lean_dec_ref(v_subst_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_957_ = stack[0].m_num;
uint8_t v_t_958_ = stack[1].m_num;
lean_object* v_args_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_957_, v_t_958_, v_args_959_, v___y_960_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* v_pu_967_, lean_object* v_t_968_, lean_object* v_args_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v_pu_boxed_972_; uint8_t v_t_boxed_973_; lean_object* v_res_974_; 
v_pu_boxed_972_ = lean_unbox(v_pu_967_);
v_t_boxed_973_ = lean_unbox(v_t_968_);
v_res_974_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_boxed_972_, v_t_boxed_973_, v_args_969_, v___y_970_);
lean_dec(v___y_970_);
return v_res_974_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_, lean_object* v___y_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
lean_inc(v___x_982_);
v___x_983_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_982_, v___y_979_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; size_t v___x_985_; size_t v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_976_, v___x_985_);
v_i_976_ = v___x_986_;
v_b_978_ = v_a_984_;
goto _start;
}
else
{
return v___x_983_;
}
}
else
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_978_);
return v___x_988_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_975_ = stack[0].m_obj;
size_t v_i_976_ = stack[1].m_num;
size_t v_stop_977_ = stack[2].m_num;
lean_object* v_b_978_ = stack[3].m_obj;
lean_object* v___y_979_ = stack[4].m_obj;
lean_object* v_res_989_;
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_975_, v_i_976_, v_stop_977_, v_b_978_, v___y_979_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_stop_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
size_t v_i_boxed_996_; size_t v_stop_boxed_997_; lean_object* v_res_998_; 
v_i_boxed_996_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_stop_boxed_997_ = lean_unbox_usize(v_stop_992_);
lean_dec(v_stop_992_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_990_, v_i_boxed_996_, v_stop_boxed_997_, v_b_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v_as_990_);
return v_res_998_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; lean_object* v___y_1005_; lean_object* v___x_1009_; 
v___x_1003_ = 1;
v___x_1009_ = lean_array_uget_borrowed(v_as_999_, v_i_1000_);
switch(lean_obj_tag(v___x_1009_))
{
case 0:
{
lean_object* v_code_1010_; 
v_code_1010_ = lean_ctor_get(v___x_1009_, 2);
v___y_1005_ = v_code_1010_;
goto v___jp_1004_;
}
case 1:
{
lean_object* v_code_1011_; 
v_code_1011_ = lean_ctor_get(v___x_1009_, 1);
v___y_1005_ = v_code_1011_;
goto v___jp_1004_;
}
default: 
{
lean_object* v_code_1012_; 
v_code_1012_ = lean_ctor_get(v___x_1009_, 0);
v___y_1005_ = v_code_1012_;
goto v___jp_1004_;
}
}
v___jp_1004_:
{
if (lean_obj_tag(v___y_1005_) == 6)
{
size_t v___x_1006_; size_t v___x_1007_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_1000_, v___x_1006_);
v_i_1000_ = v___x_1007_;
goto _start;
}
else
{
return v___x_1003_;
}
}
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = 0;
return v___x_1013_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_999_ = stack[0].m_obj;
size_t v_i_1000_ = stack[1].m_num;
size_t v_stop_1001_ = stack[2].m_num;
uint8_t v_res_1014_;
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_999_, v_i_1000_, v_stop_1001_);
stack->m_num = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_){
_start:
{
size_t v_i_boxed_1018_; size_t v_stop_boxed_1019_; uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_i_boxed_1018_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_1015_, v_i_boxed_1018_, v_stop_boxed_1019_);
lean_dec_ref(v_as_1015_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1022_, uint8_t v_t_1023_, lean_object* v_i_1024_, lean_object* v_as_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_array_get_size(v_as_1025_);
v___x_1030_ = lean_nat_dec_lt(v_i_1024_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v_i_1024_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_as_1025_);
return v___x_1031_;
}
else
{
lean_object* v_a_1032_; lean_object* v_type_1033_; lean_object* v___x_1034_; lean_object* v_subst_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1032_ = lean_array_fget_borrowed(v_as_1025_, v_i_1024_);
v_type_1033_ = lean_ctor_get(v_a_1032_, 2);
v___x_1034_ = lean_st_ref_get(v___y_1026_);
v_subst_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_subst_1035_);
lean_dec(v___x_1034_);
lean_inc_ref(v_type_1033_);
v___x_1036_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1022_, v_subst_1035_, v_t_1023_, v_type_1033_);
lean_dec_ref(v_subst_1035_);
lean_inc(v_a_1032_);
v___x_1037_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1022_, v_a_1032_, v___x_1036_, v___y_1027_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; size_t v___x_1039_; size_t v___x_1040_; uint8_t v___x_1041_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = lean_ptr_addr(v_a_1032_);
v___x_1040_ = lean_ptr_addr(v_a_1038_);
v___x_1041_ = lean_usize_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_add(v_i_1024_, v___x_1042_);
v___x_1044_ = lean_array_fset(v_as_1025_, v_i_1024_, v_a_1038_);
lean_dec(v_i_1024_);
v_i_1024_ = v___x_1043_;
v_as_1025_ = v___x_1044_;
goto _start;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v_a_1038_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v_i_1024_, v___x_1046_);
lean_dec(v_i_1024_);
v_i_1024_ = v___x_1047_;
goto _start;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_as_1025_);
lean_dec(v_i_1024_);
v_a_1049_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1037_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1037_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1022_ = stack[0].m_num;
uint8_t v_t_1023_ = stack[1].m_num;
lean_object* v_i_1024_ = stack[2].m_obj;
lean_object* v_as_1025_ = stack[3].m_obj;
lean_object* v___y_1026_ = stack[4].m_obj;
lean_object* v___y_1027_ = stack[5].m_obj;
lean_object* v_res_1057_;
v_res_1057_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1022_, v_t_1023_, v_i_1024_, v_as_1025_, v___y_1026_, v___y_1027_);
stack->m_obj
 = v_res_1057_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1058_, lean_object* v_t_1059_, lean_object* v_i_1060_, lean_object* v_as_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_pu_boxed_1065_; uint8_t v_t_boxed_1066_; lean_object* v_res_1067_; 
v_pu_boxed_1065_ = lean_unbox(v_pu_1058_);
v_t_boxed_1066_ = lean_unbox(v_t_1059_);
v_res_1067_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1065_, v_t_boxed_1066_, v_i_1060_, v_as_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec(v___y_1062_);
return v_res_1067_;
}
}
lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1068_, uint8_t v_t_1069_, lean_object* v_ps_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1068_, v_t_1069_, v___x_1079_, v_ps_1070_, v___y_1072_, v___y_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1068_ = stack[0].m_num;
uint8_t v_t_1069_ = stack[1].m_num;
lean_object* v_ps_1070_ = stack[2].m_obj;
lean_object* v___y_1071_ = stack[3].m_obj;
lean_object* v___y_1072_ = stack[4].m_obj;
lean_object* v___y_1073_ = stack[5].m_obj;
lean_object* v___y_1074_ = stack[6].m_obj;
lean_object* v___y_1075_ = stack[7].m_obj;
lean_object* v___y_1076_ = stack[8].m_obj;
lean_object* v___y_1077_ = stack[9].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_1068_, v_t_1069_, v_ps_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1082_, lean_object* v_t_1083_, lean_object* v_ps_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_pu_boxed_1093_; uint8_t v_t_boxed_1094_; lean_object* v_res_1095_; 
v_pu_boxed_1093_ = lean_unbox(v_pu_1082_);
v_t_boxed_1094_ = lean_unbox(v_t_1083_);
v_res_1095_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1093_, v_t_boxed_1094_, v_ps_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1095_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1096_, uint8_t v_t_1097_, lean_object* v_decl_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_type_1102_; lean_object* v_value_1103_; lean_object* v___x_1104_; lean_object* v_subst_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_subst_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_type_1102_ = lean_ctor_get(v_decl_1098_, 2);
v_value_1103_ = lean_ctor_get(v_decl_1098_, 3);
v___x_1104_ = lean_st_ref_get(v___y_1099_);
v_subst_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_subst_1105_);
lean_dec(v___x_1104_);
lean_inc_ref(v_type_1102_);
v___x_1106_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1096_, v_subst_1105_, v_t_1097_, v_type_1102_);
lean_dec_ref(v_subst_1105_);
v___x_1107_ = lean_st_ref_get(v___y_1099_);
v_subst_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_ref(v_subst_1108_);
lean_dec(v___x_1107_);
lean_inc(v_value_1103_);
v___x_1109_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1096_, v_subst_1108_, v_value_1103_, v_t_1097_);
lean_dec_ref(v_subst_1108_);
v___x_1110_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1096_, v_decl_1098_, v___x_1106_, v___x_1109_, v___y_1100_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1096_ = stack[0].m_num;
uint8_t v_t_1097_ = stack[1].m_num;
lean_object* v_decl_1098_ = stack[2].m_obj;
lean_object* v___y_1099_ = stack[3].m_obj;
lean_object* v___y_1100_ = stack[4].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_1096_, v_t_1097_, v_decl_1098_, v___y_1099_, v___y_1100_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1112_, lean_object* v_t_1113_, lean_object* v_decl_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_pu_boxed_1118_; uint8_t v_t_boxed_1119_; lean_object* v_res_1120_; 
v_pu_boxed_1118_ = lean_unbox(v_pu_1112_);
v_t_boxed_1119_ = lean_unbox(v_t_1113_);
v_res_1120_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1118_, v_t_boxed_1119_, v_decl_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
return v_res_1120_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1121_, lean_object* v___f_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v_fvarId_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; 
lean_inc(v_fvarId_1125_);
v___x_1131_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1125_, v___y_1121_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc_ref(v___y_1124_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1123_);
v___x_1132_ = lean_apply_9(v___f_1122_, v_fvarId_1125_, v___y_1123_, v___y_1121_, v___y_1124_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, lean_box(0));
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_fvarId_1125_);
lean_dec_ref(v___f_1122_);
v_a_1133_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1121_ = stack[0].m_obj;
lean_object* v___f_1122_ = stack[1].m_obj;
lean_object* v___y_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v_fvarId_1125_ = stack[4].m_obj;
lean_object* v___y_1126_ = stack[5].m_obj;
lean_object* v___y_1127_ = stack[6].m_obj;
lean_object* v___y_1128_ = stack[7].m_obj;
lean_object* v___y_1129_ = stack[8].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1121_, v___f_1122_, v___y_1123_, v___y_1124_, v_fvarId_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1142_, lean_object* v___f_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v_fvarId_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1142_, v___f_1143_, v___y_1144_, v___y_1145_, v_fvarId_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1142_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_ks_1157_; lean_object* v_vs_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1182_; 
v_ks_1157_ = lean_ctor_get(v_x_1153_, 0);
v_vs_1158_ = lean_ctor_get(v_x_1153_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1160_ = v_x_1153_;
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_vs_1158_);
lean_inc(v_ks_1157_);
lean_dec(v_x_1153_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1182_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_array_get_size(v_ks_1157_);
v___x_1163_ = lean_nat_dec_lt(v_x_1154_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_dec(v_x_1154_);
v___x_1164_ = lean_array_push(v_ks_1157_, v_x_1155_);
v___x_1165_ = lean_array_push(v_vs_1158_, v_x_1156_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1165_);
lean_ctor_set(v___x_1160_, 0, v___x_1164_);
v___x_1167_ = v___x_1160_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_object* v_k_x27_1169_; uint8_t v___x_1170_; 
v_k_x27_1169_ = lean_array_fget_borrowed(v_ks_1157_, v_x_1154_);
v___x_1170_ = lean_name_eq(v_x_1155_, v_k_x27_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1172_; 
if (v_isShared_1161_ == 0)
{
v___x_1172_ = v___x_1160_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_ks_1157_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_vs_1158_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_nat_add(v_x_1154_, v___x_1173_);
lean_dec(v_x_1154_);
v_x_1153_ = v___x_1172_;
v_x_1154_ = v___x_1174_;
goto _start;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1177_ = lean_array_fset(v_ks_1157_, v_x_1154_, v_x_1155_);
v___x_1178_ = lean_array_fset(v_vs_1158_, v_x_1154_, v_x_1156_);
lean_dec(v_x_1154_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1178_);
lean_ctor_set(v___x_1160_, 0, v___x_1177_);
v___x_1180_ = v___x_1160_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1183_, lean_object* v_k_1184_, lean_object* v_v_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1183_, v___x_1186_, v_k_1184_, v_v_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1188_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1189_, size_t v_x_1190_, size_t v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v_es_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v_j_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_es_1194_ = lean_ctor_get(v_x_1189_, 0);
v___x_1195_ = ((size_t)31ULL);
v___x_1196_ = lean_usize_land(v_x_1190_, v___x_1195_);
v_j_1197_ = lean_usize_to_nat(v___x_1196_);
v___x_1198_ = lean_array_get_size(v_es_1194_);
v___x_1199_ = lean_nat_dec_lt(v_j_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec(v_j_1197_);
lean_dec(v_x_1193_);
lean_dec(v_x_1192_);
return v_x_1189_;
}
else
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1238_; 
lean_inc_ref(v_es_1194_);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_x_1189_, 0);
lean_dec(v_unused_1239_);
v___x_1201_ = v_x_1189_;
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v_x_1189_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_v_1203_; lean_object* v___x_1204_; lean_object* v_xs_x27_1205_; lean_object* v___y_1207_; 
v_v_1203_ = lean_array_fget(v_es_1194_, v_j_1197_);
v___x_1204_ = lean_box(0);
v_xs_x27_1205_ = lean_array_fset(v_es_1194_, v_j_1197_, v___x_1204_);
switch(lean_obj_tag(v_v_1203_))
{
case 0:
{
lean_object* v_key_1212_; lean_object* v_val_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_key_1212_ = lean_ctor_get(v_v_1203_, 0);
v_val_1213_ = lean_ctor_get(v_v_1203_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_v_1203_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1215_ = v_v_1203_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_val_1213_);
lean_inc(v_key_1212_);
lean_dec(v_v_1203_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_name_eq(v_x_1192_, v_key_1212_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_del_object(v___x_1215_);
v___x_1218_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1212_, v_val_1213_, v_x_1192_, v_x_1193_);
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___y_1207_ = v___x_1219_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1221_; 
lean_dec(v_val_1213_);
lean_dec(v_key_1212_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_x_1193_);
lean_ctor_set(v___x_1215_, 0, v_x_1192_);
v___x_1221_ = v___x_1215_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_x_1192_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_x_1193_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1207_ = v___x_1221_;
goto v___jp_1206_;
}
}
}
}
case 1:
{
lean_object* v_node_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1236_; 
v_node_1224_ = lean_ctor_get(v_v_1203_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_v_1203_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1226_ = v_v_1203_;
v_isShared_1227_ = v_isSharedCheck_1236_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_node_1224_);
lean_dec(v_v_1203_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1236_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1228_ = ((size_t)5ULL);
v___x_1229_ = lean_usize_shift_right(v_x_1190_, v___x_1228_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_x_1191_, v___x_1230_);
v___x_1232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1224_, v___x_1229_, v___x_1231_, v_x_1192_, v_x_1193_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1232_);
v___x_1234_ = v___x_1226_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v___y_1207_ = v___x_1234_;
goto v___jp_1206_;
}
}
}
default: 
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_x_1192_);
lean_ctor_set(v___x_1237_, 1, v_x_1193_);
v___y_1207_ = v___x_1237_;
goto v___jp_1206_;
}
}
v___jp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_array_fset(v_xs_x27_1205_, v_j_1197_, v___y_1207_);
lean_dec(v_j_1197_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1208_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
lean_object* v_ks_1240_; lean_object* v_vs_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1259_; 
v_ks_1240_ = lean_ctor_get(v_x_1189_, 0);
v_vs_1241_ = lean_ctor_get(v_x_1189_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1243_ = v_x_1189_;
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_vs_1241_);
lean_inc(v_ks_1240_);
lean_dec(v_x_1189_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_ks_1240_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_vs_1241_);
v___x_1246_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v_newNode_1247_; size_t v___x_1248_; uint8_t v___x_1249_; 
v_newNode_1247_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1246_, v_x_1192_, v_x_1193_);
v___x_1248_ = ((size_t)7ULL);
v___x_1249_ = lean_usize_dec_le(v___x_1248_, v_x_1191_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1247_);
v___x_1251_ = lean_unsigned_to_nat(4u);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
if (v___x_1252_ == 0)
{
lean_object* v_ks_1253_; lean_object* v_vs_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_ks_1253_ = lean_ctor_get(v_newNode_1247_, 0);
lean_inc_ref(v_ks_1253_);
v_vs_1254_ = lean_ctor_get(v_newNode_1247_, 1);
lean_inc_ref(v_vs_1254_);
lean_dec_ref(v_newNode_1247_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1191_, v_ks_1253_, v_vs_1254_, v___x_1255_, v___x_1256_);
lean_dec_ref(v_vs_1254_);
lean_dec_ref(v_ks_1253_);
return v___x_1257_;
}
else
{
return v_newNode_1247_;
}
}
else
{
return v_newNode_1247_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1189_ = stack[0].m_obj;
size_t v_x_1190_ = stack[1].m_num;
size_t v_x_1191_ = stack[2].m_num;
lean_object* v_x_1192_ = stack[3].m_obj;
lean_object* v_x_1193_ = stack[4].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1189_, v_x_1190_, v_x_1191_, v_x_1192_, v_x_1193_);
stack->m_obj
 = v_res_1260_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1261_, lean_object* v_keys_1262_, lean_object* v_vals_1263_, lean_object* v_i_1264_, lean_object* v_entries_1265_){
_start:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_array_get_size(v_keys_1262_);
v___x_1267_ = lean_nat_dec_lt(v_i_1264_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec(v_i_1264_);
return v_entries_1265_;
}
else
{
lean_object* v_k_1268_; lean_object* v_v_1269_; uint64_t v___y_1271_; 
v_k_1268_ = lean_array_fget_borrowed(v_keys_1262_, v_i_1264_);
v_v_1269_ = lean_array_fget_borrowed(v_vals_1263_, v_i_1264_);
if (lean_obj_tag(v_k_1268_) == 0)
{
uint64_t v___x_1282_; 
v___x_1282_ = 1723ULL;
v___y_1271_ = v___x_1282_;
goto v___jp_1270_;
}
else
{
uint64_t v_hash_1283_; 
v_hash_1283_ = lean_ctor_get_uint64(v_k_1268_, sizeof(void*)*2);
v___y_1271_ = v_hash_1283_;
goto v___jp_1270_;
}
v___jp_1270_:
{
size_t v_h_1272_; size_t v___x_1273_; lean_object* v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v_h_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_h_1272_ = lean_uint64_to_usize(v___y_1271_);
v___x_1273_ = ((size_t)5ULL);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_sub(v_depth_1261_, v___x_1275_);
v___x_1277_ = lean_usize_mul(v___x_1273_, v___x_1276_);
v_h_1278_ = lean_usize_shift_right(v_h_1272_, v___x_1277_);
v___x_1279_ = lean_nat_add(v_i_1264_, v___x_1274_);
lean_dec(v_i_1264_);
lean_inc(v_v_1269_);
lean_inc(v_k_1268_);
v___x_1280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1265_, v_h_1278_, v_depth_1261_, v_k_1268_, v_v_1269_);
v_i_1264_ = v___x_1279_;
v_entries_1265_ = v___x_1280_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1261_ = stack[0].m_num;
lean_object* v_keys_1262_ = stack[1].m_obj;
lean_object* v_vals_1263_ = stack[2].m_obj;
lean_object* v_i_1264_ = stack[3].m_obj;
lean_object* v_entries_1265_ = stack[4].m_obj;
lean_object* v_res_1284_;
v_res_1284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_1261_, v_keys_1262_, v_vals_1263_, v_i_1264_, v_entries_1265_);
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1285_, lean_object* v_keys_1286_, lean_object* v_vals_1287_, lean_object* v_i_1288_, lean_object* v_entries_1289_){
_start:
{
size_t v_depth_boxed_1290_; lean_object* v_res_1291_; 
v_depth_boxed_1290_ = lean_unbox_usize(v_depth_1285_);
lean_dec(v_depth_1285_);
v_res_1291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1290_, v_keys_1286_, v_vals_1287_, v_i_1288_, v_entries_1289_);
lean_dec_ref(v_vals_1287_);
lean_dec_ref(v_keys_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
size_t v_x_43612__boxed_1297_; size_t v_x_43613__boxed_1298_; lean_object* v_res_1299_; 
v_x_43612__boxed_1297_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_x_43613__boxed_1298_ = lean_unbox_usize(v_x_1294_);
lean_dec(v_x_1294_);
v_res_1299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1292_, v_x_43612__boxed_1297_, v_x_43613__boxed_1298_, v_x_1295_, v_x_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
uint64_t v___y_1304_; 
if (lean_obj_tag(v_x_1301_) == 0)
{
uint64_t v___x_1308_; 
v___x_1308_ = 1723ULL;
v___y_1304_ = v___x_1308_;
goto v___jp_1303_;
}
else
{
uint64_t v_hash_1309_; 
v_hash_1309_ = lean_ctor_get_uint64(v_x_1301_, sizeof(void*)*2);
v___y_1304_ = v_hash_1309_;
goto v___jp_1303_;
}
v___jp_1303_:
{
size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_uint64_to_usize(v___y_1304_);
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1300_, v___x_1305_, v___x_1306_, v_x_1301_, v_x_1302_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1310_, lean_object* v_b_1311_){
_start:
{
lean_object* v_array_1312_; lean_object* v_start_1313_; lean_object* v_stop_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1327_; 
v_array_1312_ = lean_ctor_get(v_a_1310_, 0);
v_start_1313_ = lean_ctor_get(v_a_1310_, 1);
v_stop_1314_ = lean_ctor_get(v_a_1310_, 2);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1316_ = v_a_1310_;
v_isShared_1317_ = v_isSharedCheck_1327_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_stop_1314_);
lean_inc(v_start_1313_);
lean_inc(v_array_1312_);
lean_dec(v_a_1310_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1327_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_lt(v_start_1313_, v_stop_1314_);
if (v___x_1318_ == 0)
{
lean_del_object(v___x_1316_);
lean_dec(v_stop_1314_);
lean_dec(v_start_1313_);
lean_dec_ref(v_array_1312_);
return v_b_1311_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_add(v_start_1313_, v___x_1319_);
lean_inc_ref(v_array_1312_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___x_1320_);
v___x_1322_ = v___x_1316_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_array_1312_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_stop_1314_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_array_fget(v_array_1312_, v_start_1313_);
lean_dec(v_start_1313_);
lean_dec_ref(v_array_1312_);
v___x_1324_ = lean_array_push(v_b_1311_, v___x_1323_);
v_a_1310_ = v___x_1322_;
v_b_1311_ = v___x_1324_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1328_, size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_b_1331_);
return v___x_1335_;
}
else
{
lean_object* v_array_1336_; lean_object* v_start_1337_; lean_object* v_stop_1338_; uint8_t v___x_1339_; 
v_array_1336_ = lean_ctor_get(v_b_1331_, 0);
v_start_1337_ = lean_ctor_get(v_b_1331_, 1);
v_stop_1338_ = lean_ctor_get(v_b_1331_, 2);
v___x_1339_ = lean_nat_dec_lt(v_start_1337_, v_stop_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1331_);
return v___x_1340_;
}
else
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1373_; 
lean_inc(v_stop_1338_);
lean_inc(v_start_1337_);
lean_inc_ref(v_array_1336_);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_b_1331_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1374_ = lean_ctor_get(v_b_1331_, 2);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_b_1331_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_b_1331_, 0);
lean_dec(v_unused_1376_);
v___x_1342_ = v_b_1331_;
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v_b_1331_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_a_1344_; lean_object* v_fvarId_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_a_1344_ = lean_array_uget_borrowed(v_as_1328_, v_i_1330_);
v_fvarId_1345_ = lean_ctor_get(v_a_1344_, 0);
v___x_1346_ = lean_array_fget(v_array_1336_, v_start_1337_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_start_1337_, v___x_1347_);
lean_dec(v_start_1337_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___x_1348_);
v___x_1350_ = v___x_1342_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_array_1336_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_stop_1338_);
v___x_1350_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v_subst_1352_; lean_object* v_used_1353_; lean_object* v_binderRenaming_1354_; lean_object* v_funDeclInfoMap_1355_; uint8_t v_simplified_1356_; lean_object* v_visited_1357_; lean_object* v_inline_1358_; lean_object* v_inlineLocal_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1371_; 
v___x_1351_ = lean_st_ref_take(v___y_1332_);
v_subst_1352_ = lean_ctor_get(v___x_1351_, 0);
v_used_1353_ = lean_ctor_get(v___x_1351_, 1);
v_binderRenaming_1354_ = lean_ctor_get(v___x_1351_, 2);
v_funDeclInfoMap_1355_ = lean_ctor_get(v___x_1351_, 3);
v_simplified_1356_ = lean_ctor_get_uint8(v___x_1351_, sizeof(void*)*7);
v_visited_1357_ = lean_ctor_get(v___x_1351_, 4);
v_inline_1358_ = lean_ctor_get(v___x_1351_, 5);
v_inlineLocal_1359_ = lean_ctor_get(v___x_1351_, 6);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1361_ = v___x_1351_;
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_inlineLocal_1359_);
lean_inc(v_inline_1358_);
lean_inc(v_visited_1357_);
lean_inc(v_funDeclInfoMap_1355_);
lean_inc(v_binderRenaming_1354_);
lean_inc(v_used_1353_);
lean_inc(v_subst_1352_);
lean_dec(v___x_1351_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_inc(v_fvarId_1345_);
v___x_1363_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1352_, v_fvarId_1345_, v___x_1346_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_used_1353_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_binderRenaming_1354_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_funDeclInfoMap_1355_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_visited_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 5, v_inline_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 6, v_inlineLocal_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*7, v_simplified_1356_);
v___x_1365_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; 
v___x_1366_ = lean_st_ref_put(v___y_1332_, v___x_1365_);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1330_, v___x_1367_);
v_i_1330_ = v___x_1368_;
v_b_1331_ = v___x_1350_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1328_ = stack[0].m_obj;
size_t v_sz_1329_ = stack[1].m_num;
size_t v_i_1330_ = stack[2].m_num;
lean_object* v_b_1331_ = stack[3].m_obj;
lean_object* v___y_1332_ = stack[4].m_obj;
lean_object* v_res_1377_;
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1328_, v_sz_1329_, v_i_1330_, v_b_1331_, v___y_1332_);
stack->m_obj
 = v_res_1377_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1378_, lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
size_t v_sz_boxed_1384_; size_t v_i_boxed_1385_; lean_object* v_res_1386_; 
v_sz_boxed_1384_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1385_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1378_, v_sz_boxed_1384_, v_i_boxed_1385_, v_b_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v_as_1378_);
return v_res_1386_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1387_, size_t v_i_1388_, size_t v_stop_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_eq(v_i_1388_, v_stop_1389_);
if (v___x_1393_ == 0)
{
uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = 0;
v___x_1395_ = lean_array_uget_borrowed(v_as_1387_, v_i_1388_);
v___x_1396_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1394_, v___x_1395_, v___y_1391_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; size_t v___x_1398_; size_t v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1388_, v___x_1398_);
v_i_1388_ = v___x_1399_;
v_b_1390_ = v_a_1397_;
goto _start;
}
else
{
return v___x_1396_;
}
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_b_1390_);
return v___x_1401_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1387_ = stack[0].m_obj;
size_t v_i_1388_ = stack[1].m_num;
size_t v_stop_1389_ = stack[2].m_num;
lean_object* v_b_1390_ = stack[3].m_obj;
lean_object* v___y_1391_ = stack[4].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1387_, v_i_1388_, v_stop_1389_, v_b_1390_, v___y_1391_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1403_, lean_object* v_i_1404_, lean_object* v_stop_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
size_t v_i_boxed_1409_; size_t v_stop_boxed_1410_; lean_object* v_res_1411_; 
v_i_boxed_1409_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_stop_boxed_1410_ = lean_unbox_usize(v_stop_1405_);
lean_dec(v_stop_1405_);
v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1403_, v_i_boxed_1409_, v_stop_boxed_1410_, v_b_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v_as_1403_);
return v_res_1411_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1415_ = lean_panic_fn_borrowed(v___x_1414_, v_msg_1413_);
return v___x_1415_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1416_, size_t v_i_1417_, size_t v_stop_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_eq(v_i_1417_, v_stop_1418_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v_type_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = lean_array_uget_borrowed(v_as_1416_, v_i_1417_);
v_type_1423_ = lean_ctor_get(v___x_1422_, 2);
v___x_1424_ = 1;
v___x_1425_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1423_, v___y_1419_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1438_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_unbox(v_a_1426_);
lean_dec(v_a_1426_);
if (v___x_1430_ == 0)
{
size_t v___x_1431_; size_t v___x_1432_; 
lean_del_object(v___x_1428_);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1417_, v___x_1431_);
v_i_1417_ = v___x_1432_;
goto _start;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_box(v___x_1424_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1434_);
v___x_1436_ = v___x_1428_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
return v___x_1425_;
}
}
else
{
uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = 0;
v___x_1440_ = lean_box(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1416_ = stack[0].m_obj;
size_t v_i_1417_ = stack[1].m_num;
size_t v_stop_1418_ = stack[2].m_num;
lean_object* v___y_1419_ = stack[3].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1416_, v_i_1417_, v_stop_1418_, v___y_1419_);
stack->m_obj
 = v_res_1442_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1443_, lean_object* v_i_1444_, lean_object* v_stop_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
size_t v_i_boxed_1448_; size_t v_stop_boxed_1449_; lean_object* v_res_1450_; 
v_i_boxed_1448_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_stop_boxed_1449_ = lean_unbox_usize(v_stop_1445_);
lean_dec(v_stop_1445_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1443_, v_i_boxed_1448_, v_stop_boxed_1449_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v_as_1443_);
return v_res_1450_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1451_, size_t v_i_1452_, size_t v_stop_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_eq(v_i_1452_, v_stop_1453_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = 0;
v___x_1459_ = lean_array_uget_borrowed(v_as_1451_, v_i_1452_);
v___x_1460_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1458_, v___x_1459_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; size_t v___x_1462_; size_t v___x_1463_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = ((size_t)1ULL);
v___x_1463_ = lean_usize_add(v_i_1452_, v___x_1462_);
v_i_1452_ = v___x_1463_;
v_b_1454_ = v_a_1461_;
goto _start;
}
else
{
return v___x_1460_;
}
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1454_);
return v___x_1465_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1451_ = stack[0].m_obj;
size_t v_i_1452_ = stack[1].m_num;
size_t v_stop_1453_ = stack[2].m_num;
lean_object* v_b_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v_res_1466_;
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1451_, v_i_1452_, v_stop_1453_, v_b_1454_, v___y_1455_);
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1467_, lean_object* v_i_1468_, lean_object* v_stop_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
size_t v_i_boxed_1473_; size_t v_stop_boxed_1474_; lean_object* v_res_1475_; 
v_i_boxed_1473_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_stop_boxed_1474_ = lean_unbox_usize(v_stop_1469_);
lean_dec(v_stop_1469_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1467_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v_as_1467_);
return v_res_1475_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1476_, size_t v_i_1477_, size_t v_stop_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_a_1486_; lean_object* v___y_1491_; uint8_t v___x_1493_; 
v___x_1493_ = lean_usize_dec_eq(v_i_1477_, v_stop_1478_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_uget_borrowed(v_as_1476_, v_i_1477_);
v___x_1496_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1495_);
v___x_1497_ = lean_array_get_size(v___x_1496_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_nat_dec_lt(v___x_1494_, v___x_1497_);
if (v___x_1499_ == 0)
{
lean_dec_ref(v___x_1496_);
v_a_1486_ = v___x_1498_;
goto v___jp_1485_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_nat_dec_le(v___x_1497_, v___x_1497_);
if (v___x_1500_ == 0)
{
if (v___x_1499_ == 0)
{
lean_dec_ref(v___x_1496_);
v_a_1486_ = v___x_1498_;
goto v___jp_1485_;
}
else
{
size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = lean_usize_of_nat(v___x_1497_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1496_, v___x_1501_, v___x_1502_, v___x_1498_, v___y_1481_);
lean_dec_ref(v___x_1496_);
v___y_1491_ = v___x_1503_;
goto v___jp_1490_;
}
}
else
{
size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = lean_usize_of_nat(v___x_1497_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1496_, v___x_1504_, v___x_1505_, v___x_1498_, v___y_1481_);
lean_dec_ref(v___x_1496_);
v___y_1491_ = v___x_1506_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_b_1479_);
return v___x_1507_;
}
v___jp_1485_:
{
size_t v___x_1487_; size_t v___x_1488_; 
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1477_, v___x_1487_);
v_i_1477_ = v___x_1488_;
v_b_1479_ = v_a_1486_;
goto _start;
}
v___jp_1490_:
{
if (lean_obj_tag(v___y_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___y_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___y_1491_, 1);
v_a_1486_ = v_a_1492_;
goto v___jp_1485_;
}
else
{
return v___y_1491_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1476_ = stack[0].m_obj;
size_t v_i_1477_ = stack[1].m_num;
size_t v_stop_1478_ = stack[2].m_num;
lean_object* v_b_1479_ = stack[3].m_obj;
lean_object* v___y_1480_ = stack[4].m_obj;
lean_object* v___y_1481_ = stack[5].m_obj;
lean_object* v___y_1482_ = stack[6].m_obj;
lean_object* v___y_1483_ = stack[7].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1476_, v_i_1477_, v_stop_1478_, v_b_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_stop_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_i_boxed_1518_; size_t v_stop_boxed_1519_; lean_object* v_res_1520_; 
v_i_boxed_1518_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_stop_boxed_1519_ = lean_unbox_usize(v_stop_1511_);
lean_dec(v_stop_1511_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1509_, v_i_boxed_1518_, v_stop_boxed_1519_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_as_1509_);
return v_res_1520_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1521_, size_t v_i_1522_, size_t v_stop_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_usize_dec_eq(v_i_1522_, v_stop_1523_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v_fvarId_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_array_uget_borrowed(v_as_1521_, v_i_1522_);
v_fvarId_1528_ = lean_ctor_get(v___x_1527_, 0);
v___x_1529_ = 1;
v___x_1530_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1528_, v___y_1524_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1543_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_unbox(v_a_1531_);
lean_dec(v_a_1531_);
if (v___x_1535_ == 0)
{
size_t v___x_1536_; size_t v___x_1537_; 
lean_del_object(v___x_1533_);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1522_, v___x_1536_);
v_i_1522_ = v___x_1537_;
goto _start;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_box(v___x_1529_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1539_);
v___x_1541_ = v___x_1533_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
return v___x_1530_;
}
}
else
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = 0;
v___x_1545_ = lean_box(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1521_ = stack[0].m_obj;
size_t v_i_1522_ = stack[1].m_num;
size_t v_stop_1523_ = stack[2].m_num;
lean_object* v___y_1524_ = stack[3].m_obj;
lean_object* v_res_1547_;
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1521_, v_i_1522_, v_stop_1523_, v___y_1524_);
stack->m_obj
 = v_res_1547_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1548_, lean_object* v_i_1549_, lean_object* v_stop_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
size_t v_i_boxed_1553_; size_t v_stop_boxed_1554_; lean_object* v_res_1555_; 
v_i_boxed_1553_ = lean_unbox_usize(v_i_1549_);
lean_dec(v_i_1549_);
v_stop_boxed_1554_ = lean_unbox_usize(v_stop_1550_);
lean_dec(v_stop_1550_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1548_, v_i_boxed_1553_, v_stop_boxed_1554_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v_as_1548_);
return v_res_1555_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1560_ = lean_unsigned_to_nat(9u);
v___x_1561_ = lean_unsigned_to_nat(650u);
v___x_1562_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1563_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1564_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_);
return v___x_1564_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_fvarId_1570_, lean_object* v_k_1571_, lean_object* v_args_1572_, uint8_t v___x_1573_, lean_object* v___x_1574_, lean_object* v_result_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_lower_1585_; lean_object* v_upper_1586_; uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec(v___x_1574_);
lean_dec_ref(v_args_1572_);
lean_dec(v___x_1569_);
lean_dec(v___x_1568_);
v___x_1614_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1570_, v_result_1575_, v___y_1577_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1614_, 1);
lean_inc_ref(v___y_1581_);
v___x_1615_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1571_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1615_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_k_1571_);
v_a_1616_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1614_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1614_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_le(v___x_1568_, v___x_1574_);
if (v___x_1624_ == 0)
{
lean_dec(v___x_1574_);
v_lower_1585_ = v___x_1568_;
v_upper_1586_ = v___x_1569_;
goto v___jp_1584_;
}
else
{
lean_dec(v___x_1568_);
v_lower_1585_ = v___x_1574_;
v_upper_1586_ = v___x_1569_;
goto v___jp_1584_;
}
}
v___jp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1587_ = l_Array_toSubarray___redArg(v_args_1572_, v_lower_1585_, v_upper_1586_);
v___x_1588_ = l_Subarray_copy___redArg(v___x_1587_);
v___x_1589_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_result_1575_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1591_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1573_, v___x_1589_, v___x_1590_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_fvarId_1593_; lean_object* v___x_1594_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_fvarId_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_fvarId_1593_);
v___x_1594_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1570_, v_fvarId_1593_, v___y_1577_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref_known(v___x_1594_, 1);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_a_1592_);
lean_ctor_set(v___x_1595_, 1, v_k_1571_);
lean_inc_ref(v___y_1581_);
v___x_1596_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1595_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1596_;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_a_1592_);
lean_dec_ref(v_k_1571_);
v_a_1597_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1594_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1594_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v_k_1571_);
lean_dec(v_fvarId_1570_);
v_a_1605_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1591_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1591_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1568_ = stack[0].m_obj;
lean_object* v___x_1569_ = stack[1].m_obj;
lean_object* v_fvarId_1570_ = stack[2].m_obj;
lean_object* v_k_1571_ = stack[3].m_obj;
lean_object* v_args_1572_ = stack[4].m_obj;
uint8_t v___x_1573_ = stack[5].m_num;
lean_object* v___x_1574_ = stack[6].m_obj;
lean_object* v_result_1575_ = stack[7].m_obj;
lean_object* v___y_1576_ = stack[8].m_obj;
lean_object* v___y_1577_ = stack[9].m_obj;
lean_object* v___y_1578_ = stack[10].m_obj;
lean_object* v___y_1579_ = stack[11].m_obj;
lean_object* v___y_1580_ = stack[12].m_obj;
lean_object* v___y_1581_ = stack[13].m_obj;
lean_object* v___y_1582_ = stack[14].m_obj;
lean_object* v_res_1625_;
v_res_1625_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1568_, v___x_1569_, v_fvarId_1570_, v_k_1571_, v_args_1572_, v___x_1573_, v___x_1574_, v_result_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
stack->m_obj
 = v_res_1625_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1626_, lean_object* v___x_1627_, lean_object* v_fvarId_1628_, lean_object* v_k_1629_, lean_object* v_args_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, lean_object* v_result_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
uint8_t v___x_44384__boxed_1642_; lean_object* v_res_1643_; 
v___x_44384__boxed_1642_ = lean_unbox(v___x_1631_);
v_res_1643_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1626_, v___x_1627_, v_fvarId_1628_, v_k_1629_, v_args_1630_, v___x_44384__boxed_1642_, v___x_1632_, v_result_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1643_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1644_, lean_object* v_k_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_fvarId_1654_; lean_object* v_value_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1993_; 
v_fvarId_1654_ = lean_ctor_get(v_letDecl_1644_, 0);
v_value_1655_ = lean_ctor_get(v_letDecl_1644_, 3);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_letDecl_1644_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; lean_object* v_unused_1995_; 
v_unused_1994_ = lean_ctor_get(v_letDecl_1644_, 2);
lean_dec(v_unused_1994_);
v_unused_1995_ = lean_ctor_get(v_letDecl_1644_, 1);
lean_dec(v_unused_1995_);
v___x_1657_ = v_letDecl_1644_;
v_isShared_1658_ = v_isSharedCheck_1993_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_value_1655_);
lean_inc(v_fvarId_1654_);
lean_dec(v_letDecl_1644_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1993_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
lean_inc(v_value_1655_);
v___x_1659_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1655_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1984_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1984_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1984_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
if (lean_obj_tag(v_a_1660_) == 1)
{
lean_object* v_val_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1662_);
v_val_1664_ = lean_ctor_get(v_a_1660_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1666_ = v_a_1660_;
v_isShared_1667_ = v_isSharedCheck_1979_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_val_1664_);
lean_dec(v_a_1660_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1979_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_params_1668_; lean_object* v_value_1669_; lean_object* v_fType_1670_; lean_object* v_args_1671_; uint8_t v_recursive_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; 
v_params_1668_ = lean_ctor_get(v_val_1664_, 0);
v_value_1669_ = lean_ctor_get(v_val_1664_, 1);
v_fType_1670_ = lean_ctor_get(v_val_1664_, 2);
v_args_1671_ = lean_ctor_get(v_val_1664_, 3);
v_recursive_1672_ = lean_ctor_get_uint8(v_val_1664_, sizeof(void*)*4 + 2);
v___x_1673_ = lean_array_get_size(v_args_1671_);
v___x_1674_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1664_);
v___x_1675_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
if (lean_obj_tag(v_value_1655_) == 3)
{
lean_object* v_declName_1959_; lean_object* v___x_1960_; 
v_declName_1959_ = lean_ctor_get(v_value_1655_, 0);
lean_inc_n(v_declName_1959_, 2);
lean_dec_ref_known(v_value_1655_, 3);
v___x_1960_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1672_, v_declName_1959_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v_declName_1962_; lean_object* v_config_1963_; lean_object* v_inlineStack_1964_; lean_object* v_inlineStackOccs_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v_declName_1962_ = lean_ctor_get(v_a_1646_, 0);
v_config_1963_ = lean_ctor_get(v_a_1646_, 1);
v_inlineStack_1964_ = lean_ctor_get(v_a_1646_, 2);
v_inlineStackOccs_1965_ = lean_ctor_get(v_a_1646_, 3);
lean_inc(v_inlineStack_1964_);
lean_inc(v_declName_1959_);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_declName_1959_);
lean_ctor_set(v___x_1966_, 1, v_inlineStack_1964_);
lean_inc_ref(v_inlineStackOccs_1965_);
v___x_1967_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1965_, v_declName_1959_, v_a_1961_);
lean_inc_ref(v_config_1963_);
lean_inc(v_declName_1962_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 3, v___x_1967_);
lean_ctor_set(v___x_1657_, 2, v___x_1966_);
lean_ctor_set(v___x_1657_, 1, v_config_1963_);
lean_ctor_set(v___x_1657_, 0, v_declName_1962_);
v___x_1969_ = v___x_1657_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_declName_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_config_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
v___y_1858_ = v___x_1969_;
v___y_1859_ = v_a_1647_;
v___y_1860_ = v_a_1648_;
v___y_1861_ = v_a_1649_;
v___y_1862_ = v_a_1650_;
v___y_1863_ = v_a_1651_;
v___y_1864_ = v_a_1652_;
goto v___jp_1857_;
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_declName_1959_);
lean_dec(v___x_1674_);
lean_del_object(v___x_1666_);
lean_dec(v_val_1664_);
lean_del_object(v___x_1657_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
v_a_1971_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1960_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1960_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_del_object(v___x_1657_);
lean_dec(v_value_1655_);
lean_inc_ref(v_a_1646_);
v___y_1858_ = v_a_1646_;
v___y_1859_ = v_a_1647_;
v___y_1860_ = v_a_1648_;
v___y_1861_ = v_a_1649_;
v___y_1862_ = v_a_1650_;
v___y_1863_ = v_a_1651_;
v___y_1864_ = v_a_1652_;
goto v___jp_1857_;
}
v___jp_1676_:
{
lean_object* v___x_1690_; 
lean_inc_ref(v___y_1685_);
v___x_1690_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1679_, v___y_1681_, v___y_1683_, v___y_1686_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1683_);
if (lean_obj_tag(v___x_1692_) == 0)
{
uint8_t v___x_1693_; 
lean_dec_ref_known(v___x_1692_, 1);
v___x_1693_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1691_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec_ref(v___y_1678_);
v___x_1694_ = lean_mk_empty_array_with_capacity(v___y_1682_);
lean_dec(v___y_1682_);
lean_inc_ref(v___x_1694_);
v___x_1695_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1687_, v___x_1694_);
v___x_1696_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1688_, v_fType_1670_, v___x_1695_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc_n(v_a_1697_, 2);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l_Lean_Expr_headBeta(v_a_1697_);
v___x_1699_ = l_Lean_Expr_isForall(v___x_1698_);
lean_dec_ref(v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec_ref(v___x_1694_);
v___x_1700_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1688_, v_a_1697_, v___x_1675_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v_fvarId_1702_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v_fvarId_1702_ = lean_ctor_get(v_a_1701_, 0);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1677_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1683_);
lean_inc(v_fvarId_1702_);
v___x_1703_ = lean_apply_9(v___y_1689_, v_fvarId_1702_, v___y_1681_, v___y_1683_, v___y_1686_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_, lean_box(0));
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = lean_mk_empty_array_with_capacity(v___x_1705_);
v___x_1707_ = lean_array_push(v___x_1706_, v_a_1701_);
v___x_1708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1709_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1688_, v___x_1707_, v_a_1704_, v___x_1708_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_n(v_a_1710_, 2);
lean_dec_ref_known(v___x_1709_, 1);
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1711_, 0, v_a_1710_);
lean_closure_set(v___f_1711_, 1, v___x_1705_);
v___x_1712_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1688_, v_a_1691_, v___f_1711_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1724_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1724_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_a_1710_);
lean_ctor_set(v___x_1717_, 1, v_a_1713_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1717_);
v___x_1719_ = v___x_1666_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1719_);
v___x_1721_ = v___x_1715_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1710_);
lean_del_object(v___x_1666_);
v_a_1725_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1712_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1712_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1691_);
lean_del_object(v___x_1666_);
v_a_1733_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1709_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1709_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1701_);
lean_dec(v_a_1691_);
lean_del_object(v___x_1666_);
v_a_1741_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1703_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1703_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
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
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1691_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1681_);
lean_del_object(v___x_1666_);
v_a_1749_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1700_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1700_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v_a_1697_);
v___x_1757_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1758_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1694_, v_a_1691_, v___x_1757_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1759_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v_fvarId_1762_; lean_object* v___x_1763_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v_fvarId_1762_ = lean_ctor_get(v_a_1761_, 0);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1677_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1681_);
lean_inc(v_fvarId_1762_);
v___x_1763_ = lean_apply_9(v___y_1689_, v_fvarId_1762_, v___y_1681_, v___y_1683_, v___y_1686_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_, lean_box(0));
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1761_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_mk_empty_array_with_capacity(v___x_1766_);
v___x_1768_ = lean_array_push(v___x_1767_, v___x_1765_);
v___x_1769_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1768_, v_a_1764_, v___y_1681_, v___y_1683_, v___y_1686_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___x_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1780_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_a_1770_);
v___x_1775_ = v___x_1666_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1666_);
v_a_1781_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1769_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1769_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_a_1761_);
lean_dec_ref(v___y_1681_);
lean_del_object(v___x_1666_);
v_a_1789_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1763_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1763_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1681_);
lean_del_object(v___x_1666_);
v_a_1797_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1760_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1760_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1681_);
lean_del_object(v___x_1666_);
v_a_1805_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1758_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1758_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
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
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v___x_1694_);
lean_dec(v_a_1691_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1681_);
lean_del_object(v___x_1666_);
v_a_1813_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1696_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1696_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v_fType_1670_);
v___x_1821_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1688_, v_a_1691_, v___y_1678_, v___y_1677_, v___y_1680_, v___y_1685_, v___y_1684_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_a_1822_);
v___x_1827_ = v___x_1666_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_del_object(v___x_1666_);
v_a_1833_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1821_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1691_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_fType_1670_);
lean_del_object(v___x_1666_);
v_a_1841_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1692_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1692_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v___y_1689_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_fType_1670_);
lean_del_object(v___x_1666_);
v_a_1849_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1690_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1690_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
v___jp_1857_:
{
if (v___x_1675_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_inc_ref_n(v_args_1671_, 2);
lean_inc_ref(v_fType_1670_);
lean_inc_ref(v_value_1669_);
lean_inc_ref(v_params_1668_);
lean_dec(v_val_1664_);
v___x_1865_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1674_);
v___x_1866_ = l_Array_toSubarray___redArg(v_args_1671_, v___x_1865_, v___x_1674_);
lean_inc_ref(v___x_1866_);
v___x_1867_ = l_Subarray_copy___redArg(v___x_1866_);
v___x_1868_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1668_, v_value_1669_, v___x_1867_, v___x_1675_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v_params_1668_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___f_1872_; lean_object* v___f_1873_; uint8_t v___x_1874_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = 0;
v___x_1871_ = lean_box(v___x_1870_);
lean_inc_ref(v_k_1645_);
lean_inc(v_fvarId_1654_);
lean_inc(v___x_1674_);
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1872_, 0, v___x_1674_);
lean_closure_set(v___f_1872_, 1, v___x_1673_);
lean_closure_set(v___f_1872_, 2, v_fvarId_1654_);
lean_closure_set(v___f_1872_, 3, v_k_1645_);
lean_closure_set(v___f_1872_, 4, v_args_1671_);
lean_closure_set(v___f_1872_, 5, v___x_1871_);
lean_closure_set(v___f_1872_, 6, v___x_1865_);
lean_inc_ref(v___y_1860_);
lean_inc_ref(v___y_1858_);
lean_inc_ref(v___f_1872_);
lean_inc(v___y_1859_);
v___f_1873_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1873_, 0, v___y_1859_);
lean_closure_set(v___f_1873_, 1, v___f_1872_);
lean_closure_set(v___f_1873_, 2, v___y_1858_);
lean_closure_set(v___f_1873_, 3, v___y_1860_);
v___x_1874_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1645_, v_fvarId_1654_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
if (v___x_1874_ == 0)
{
lean_dec(v___x_1674_);
v___y_1677_ = v___y_1861_;
v___y_1678_ = v___f_1873_;
v___y_1679_ = v_a_1869_;
v___y_1680_ = v___y_1862_;
v___y_1681_ = v___y_1858_;
v___y_1682_ = v___x_1865_;
v___y_1683_ = v___y_1859_;
v___y_1684_ = v___y_1864_;
v___y_1685_ = v___y_1863_;
v___y_1686_ = v___y_1860_;
v___y_1687_ = v___x_1866_;
v___y_1688_ = v___x_1870_;
v___y_1689_ = v___f_1872_;
goto v___jp_1676_;
}
else
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_eq(v___x_1673_, v___x_1674_);
lean_dec(v___x_1674_);
if (v___x_1875_ == 0)
{
v___y_1677_ = v___y_1861_;
v___y_1678_ = v___f_1873_;
v___y_1679_ = v_a_1869_;
v___y_1680_ = v___y_1862_;
v___y_1681_ = v___y_1858_;
v___y_1682_ = v___x_1865_;
v___y_1683_ = v___y_1859_;
v___y_1684_ = v___y_1864_;
v___y_1685_ = v___y_1863_;
v___y_1686_ = v___y_1860_;
v___y_1687_ = v___x_1866_;
v___y_1688_ = v___x_1870_;
v___y_1689_ = v___f_1872_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1876_; 
lean_dec_ref(v___f_1873_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_fType_1670_);
lean_del_object(v___x_1666_);
v___x_1876_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1859_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; 
lean_dec_ref_known(v___x_1876_, 1);
lean_inc_ref(v___y_1863_);
v___x_1877_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1869_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___y_1858_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1886_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
v_a_1887_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1877_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1877_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1869_);
lean_dec_ref(v___y_1858_);
v_a_1895_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1876_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1876_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v___x_1866_);
lean_dec_ref(v___y_1858_);
lean_dec(v___x_1674_);
lean_dec_ref(v_args_1671_);
lean_dec_ref(v_fType_1670_);
lean_del_object(v___x_1666_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
v_a_1903_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1868_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1868_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v___x_1911_; 
lean_dec(v___x_1674_);
lean_del_object(v___x_1666_);
v___x_1911_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1664_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_fvarId_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v_fvarId_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc(v_fvarId_1913_);
v___x_1914_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1654_, v_fvarId_1913_, v___y_1859_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v___x_1914_, 1);
v___x_1915_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1859_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1915_, 1);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_a_1912_);
lean_ctor_set(v___x_1916_, 1, v_k_1645_);
lean_inc_ref(v___y_1863_);
v___x_1917_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1916_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___y_1858_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_a_1927_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1917_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1917_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1912_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v_k_1645_);
v_a_1935_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1915_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1915_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_a_1912_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v_k_1645_);
v_a_1943_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1914_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1914_);
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
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v___y_1858_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
v_a_1951_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1911_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1911_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_dec(v_a_1660_);
lean_del_object(v___x_1657_);
lean_dec(v_value_1655_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
v___x_1980_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1980_);
v___x_1982_ = v___x_1662_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_del_object(v___x_1657_);
lean_dec(v_value_1655_);
lean_dec(v_fvarId_1654_);
lean_dec_ref(v_k_1645_);
v_a_1985_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1659_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1659_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_letDecl_1644_ = stack[0].m_obj;
lean_object* v_k_1645_ = stack[1].m_obj;
lean_object* v_a_1646_ = stack[2].m_obj;
lean_object* v_a_1647_ = stack[3].m_obj;
lean_object* v_a_1648_ = stack[4].m_obj;
lean_object* v_a_1649_ = stack[5].m_obj;
lean_object* v_a_1650_ = stack[6].m_obj;
lean_object* v_a_1651_ = stack[7].m_obj;
lean_object* v_a_1652_ = stack[8].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_1644_, v_k_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
stack->m_obj
 = v_res_1996_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1997_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_typeName_2010_; lean_object* v_discr_2011_; uint8_t v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_subst_2016_; lean_object* v___x_2017_; 
v_typeName_2010_ = lean_ctor_get(v_cases_1998_, 0);
v_discr_2011_ = lean_ctor_get(v_cases_1998_, 2);
v___x_2012_ = 0;
v___x_2013_ = 0;
v___x_2014_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2015_ = lean_st_ref_get(v_a_2000_);
v_subst_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_subst_2016_);
lean_dec(v___x_2015_);
lean_inc(v_discr_2011_);
v___x_2017_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2016_, v_discr_2011_, v___x_2013_);
lean_dec_ref(v_subst_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_fvarId_2018_; lean_object* v___x_2019_; 
v_fvarId_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_fvarId_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_2018_, v_a_2001_, v_a_2003_, v_a_2005_);
lean_dec(v_fvarId_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2248_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2248_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2248_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
if (lean_obj_tag(v_a_2020_) == 1)
{
lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2243_; 
v_val_2024_ = lean_ctor_get(v_a_2020_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2026_ = v_a_2020_;
v_isShared_2027_ = v_isSharedCheck_2243_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v_a_2020_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2243_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v_env_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = lean_st_ref_get(v_a_2005_);
v_env_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2028_);
v___x_2030_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_2024_);
lean_inc(v___x_2030_);
v___x_2031_ = l_Lean_Environment_find_x3f(v_env_2029_, v___x_2030_, v___x_2013_);
if (lean_obj_tag(v___x_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2242_; 
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2242_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2242_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
if (lean_obj_tag(v_val_2032_) == 6)
{
lean_object* v_val_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2241_; 
v_val_2036_ = lean_ctor_get(v_val_2032_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_val_2032_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2038_ = v_val_2032_;
v_isShared_2039_ = v_isSharedCheck_2241_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_val_2036_);
lean_dec(v_val_2032_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2241_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_induct_2040_; uint8_t v___x_2041_; 
v_induct_2040_ = lean_ctor_get(v_val_2036_, 1);
lean_inc(v_induct_2040_);
lean_dec_ref(v_val_2036_);
v___x_2041_ = lean_name_eq(v_typeName_2010_, v_induct_2040_);
lean_dec(v_induct_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_del_object(v___x_2038_);
lean_del_object(v___x_2034_);
lean_dec(v___x_2030_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
lean_dec_ref(v_cases_1998_);
v___x_2042_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2042_);
v___x_2044_ = v___x_2022_;
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
else
{
lean_object* v___x_2046_; lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2240_; 
lean_del_object(v___x_2022_);
v___x_2046_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_2012_, v_cases_1998_, v___x_2030_);
v_fst_2047_ = lean_ctor_get(v___x_2046_, 0);
v_snd_2048_ = lean_ctor_get(v___x_2046_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2050_ = v___x_2046_;
v_isShared_2051_ = v_isSharedCheck_2240_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_snd_2048_);
lean_inc(v_fst_2047_);
lean_dec(v___x_2046_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2240_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 4);
lean_ctor_set(v___x_2038_, 0, v_snd_2048_);
v___x_2053_ = v___x_2038_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_snd_2048_);
v___x_2053_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2012_, v___x_2053_, v_a_2003_);
lean_dec_ref(v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; 
lean_dec_ref_known(v___x_2054_, 1);
v___x_2055_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2000_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
if (lean_obj_tag(v_fst_2047_) == 0)
{
if (lean_obj_tag(v_val_2024_) == 0)
{
lean_object* v_params_2056_; lean_object* v_code_2057_; lean_object* v_val_2058_; lean_object* v_args_2059_; lean_object* v_lower_2061_; lean_object* v_upper_2062_; lean_object* v_numParams_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
lean_del_object(v___x_2050_);
lean_del_object(v___x_2026_);
v_params_2056_ = lean_ctor_get(v_fst_2047_, 1);
lean_inc_ref(v_params_2056_);
v_code_2057_ = lean_ctor_get(v_fst_2047_, 2);
lean_inc_ref(v_code_2057_);
lean_dec_ref_known(v_fst_2047_, 3);
v_val_2058_ = lean_ctor_get(v_val_2024_, 0);
lean_inc_ref(v_val_2058_);
v_args_2059_ = lean_ctor_get(v_val_2024_, 1);
lean_inc_ref(v_args_2059_);
lean_dec_ref_known(v_val_2024_, 2);
v_numParams_2105_ = lean_ctor_get(v_val_2058_, 3);
lean_inc(v_numParams_2105_);
lean_dec_ref(v_val_2058_);
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_array_get_size(v_args_2059_);
v___x_2108_ = lean_nat_dec_le(v_numParams_2105_, v___x_2106_);
if (v___x_2108_ == 0)
{
v_lower_2061_ = v_numParams_2105_;
v_upper_2062_ = v___x_2107_;
goto v___jp_2060_;
}
else
{
lean_dec(v_numParams_2105_);
v_lower_2061_ = v___x_2106_;
v_upper_2062_ = v___x_2107_;
goto v___jp_2060_;
}
v___jp_2060_:
{
lean_object* v___x_2063_; size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = l_Array_toSubarray___redArg(v_args_2059_, v_lower_2061_, v_upper_2062_);
v_sz_2064_ = lean_array_size(v_params_2056_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2056_, v_sz_2064_, v___x_2065_, v___x_2063_, v_a_2000_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref_known(v___x_2066_, 1);
lean_inc_ref(v_a_2004_);
v___x_2067_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2057_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2012_, v_params_2056_, v_a_2003_);
lean_dec_ref(v_params_2056_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v___x_2069_, 0);
lean_dec(v_unused_2080_);
v___x_2071_ = v___x_2069_;
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v___x_2069_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2068_);
v___x_2074_ = v___x_2034_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2068_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2074_);
v___x_2076_ = v___x_2071_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
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
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_2068_);
lean_del_object(v___x_2034_);
v_a_2081_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2069_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2069_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_params_2056_);
lean_del_object(v___x_2034_);
v_a_2089_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2067_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2067_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_code_2057_);
lean_dec_ref(v_params_2056_);
lean_del_object(v___x_2034_);
v_a_2097_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2066_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2066_);
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
}
else
{
lean_object* v_params_2109_; lean_object* v_code_2110_; lean_object* v_n_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2201_; 
v_params_2109_ = lean_ctor_get(v_fst_2047_, 1);
lean_inc_ref(v_params_2109_);
v_code_2110_ = lean_ctor_get(v_fst_2047_, 2);
lean_inc_ref(v_code_2110_);
lean_dec_ref_known(v_fst_2047_, 3);
v_n_2111_ = lean_ctor_get(v_val_2024_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_val_2024_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2113_ = v_val_2024_;
v_isShared_2114_ = v_isSharedCheck_2201_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_n_2111_);
lean_dec(v_val_2024_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2201_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_zero_2115_; uint8_t v_isZero_2116_; 
v_zero_2115_ = lean_unsigned_to_nat(0u);
v_isZero_2116_ = lean_nat_dec_eq(v_n_2111_, v_zero_2115_);
if (v_isZero_2116_ == 1)
{
lean_object* v___x_2117_; 
lean_del_object(v___x_2113_);
lean_dec(v_n_2111_);
lean_dec_ref(v_params_2109_);
lean_del_object(v___x_2050_);
lean_del_object(v___x_2026_);
lean_inc_ref(v_a_2004_);
v___x_2117_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2110_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2118_);
v___x_2123_ = v___x_2034_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_del_object(v___x_2034_);
v_a_2129_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2117_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2117_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_one_2137_; lean_object* v_n_2138_; lean_object* v___x_2140_; 
v_one_2137_ = lean_unsigned_to_nat(1u);
v_n_2138_ = lean_nat_sub(v_n_2111_, v_one_2137_);
lean_dec(v_n_2111_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 0);
lean_ctor_set(v___x_2113_, 0, v_n_2138_);
v___x_2140_ = v___x_2113_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_n_2138_);
v___x_2140_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2140_);
v___x_2142_ = v___x_2026_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2144_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_2012_, v___x_2142_, v___x_2143_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v_fvarId_2147_; lean_object* v_fvarId_2148_; lean_object* v___x_2149_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_array_get_borrowed(v___x_2014_, v_params_2109_, v_zero_2115_);
v_fvarId_2147_ = lean_ctor_get(v___x_2146_, 0);
v_fvarId_2148_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_fvarId_2148_);
lean_inc(v_fvarId_2147_);
v___x_2149_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2147_, v_fvarId_2148_, v_a_2000_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; 
lean_dec_ref_known(v___x_2149_, 1);
lean_inc_ref(v_a_2004_);
v___x_2150_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2110_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2012_, v_params_2109_, v_a_2003_);
lean_dec_ref(v_params_2109_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2165_; 
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2152_, 0);
lean_dec(v_unused_2166_);
v___x_2154_ = v___x_2152_;
v_isShared_2155_ = v_isSharedCheck_2165_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v___x_2152_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2165_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v_a_2151_);
lean_ctor_set(v___x_2050_, 0, v_a_2145_);
v___x_2157_ = v___x_2050_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_a_2151_);
v___x_2157_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2157_);
v___x_2159_ = v___x_2034_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2159_);
v___x_2161_ = v___x_2154_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
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
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2151_);
lean_dec(v_a_2145_);
lean_del_object(v___x_2050_);
lean_del_object(v___x_2034_);
v_a_2167_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2152_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2152_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_params_2109_);
lean_del_object(v___x_2050_);
lean_del_object(v___x_2034_);
v_a_2175_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2150_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2150_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
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
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_code_2110_);
lean_dec_ref(v_params_2109_);
lean_del_object(v___x_2050_);
lean_del_object(v___x_2034_);
v_a_2183_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2149_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2149_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_code_2110_);
lean_dec_ref(v_params_2109_);
lean_del_object(v___x_2050_);
lean_del_object(v___x_2034_);
v_a_2191_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2144_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2144_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
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
lean_object* v_code_2202_; lean_object* v___x_2203_; 
lean_del_object(v___x_2050_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
v_code_2202_ = lean_ctor_get(v_fst_2047_, 0);
lean_inc_ref(v_code_2202_);
lean_dec_ref_known(v_fst_2047_, 1);
lean_inc_ref(v_a_2004_);
v___x_2203_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2202_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2214_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2204_);
v___x_2209_ = v___x_2034_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2209_);
v___x_2211_ = v___x_2206_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_del_object(v___x_2034_);
v_a_2215_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2203_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2203_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2050_);
lean_dec(v_fst_2047_);
lean_del_object(v___x_2034_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
v_a_2223_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2055_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2055_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_del_object(v___x_2050_);
lean_dec(v_fst_2047_);
lean_del_object(v___x_2034_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
v_a_2231_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2054_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2054_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
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
lean_del_object(v___x_2034_);
lean_dec(v_val_2032_);
lean_dec(v___x_2030_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_cases_1998_);
goto v___jp_2007_;
}
}
}
else
{
lean_dec(v___x_2031_);
lean_dec(v___x_2030_);
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_cases_1998_);
goto v___jp_2007_;
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_dec(v_a_2020_);
lean_dec_ref(v_cases_1998_);
v___x_2244_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2244_);
v___x_2246_ = v___x_2022_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_cases_1998_);
v_a_2249_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2019_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2019_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v___x_2257_; 
lean_dec_ref(v_cases_1998_);
v___x_2257_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2012_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2266_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_a_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2257_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2257_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
v___jp_2007_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_cases_1998_ = stack[0].m_obj;
lean_object* v_a_1999_ = stack[1].m_obj;
lean_object* v_a_2000_ = stack[2].m_obj;
lean_object* v_a_2001_ = stack[3].m_obj;
lean_object* v_a_2002_ = stack[4].m_obj;
lean_object* v_a_2003_ = stack[5].m_obj;
lean_object* v_a_2004_ = stack[6].m_obj;
lean_object* v_a_2005_ = stack[7].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
stack->m_obj
 = v_res_2275_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2276_, lean_object* v_i_2277_, lean_object* v_as_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = lean_array_get_size(v_as_2278_);
v___x_2288_ = lean_nat_dec_lt(v_i_2277_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_as_2278_);
return v___x_2289_;
}
else
{
lean_object* v_a_2290_; lean_object* v_a_2292_; 
v_a_2290_ = lean_array_fget_borrowed(v_as_2278_, v_i_2277_);
if (lean_obj_tag(v_a_2290_) == 0)
{
lean_object* v_ctorName_2303_; lean_object* v_params_2304_; lean_object* v_code_2305_; uint8_t v___x_2328_; uint8_t v_a_2330_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_ctorName_2303_ = lean_ctor_get(v_a_2290_, 0);
v_params_2304_ = lean_ctor_get(v_a_2290_, 1);
v_code_2305_ = lean_ctor_get(v_a_2290_, 2);
v___x_2328_ = 0;
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_array_get_size(v_params_2304_);
v___x_2363_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
v_a_2330_ = v___x_2363_;
goto v___jp_2329_;
}
else
{
if (v___x_2363_ == 0)
{
v_a_2330_ = v___x_2363_;
goto v___jp_2329_;
}
else
{
size_t v___x_2364_; size_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = lean_usize_of_nat(v___x_2362_);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2304_, v___x_2364_, v___x_2365_, v___y_2285_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; uint8_t v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_unbox(v_a_2367_);
lean_dec(v_a_2367_);
v_a_2330_ = v___x_2368_;
goto v___jp_2329_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2369_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2366_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2366_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
v___jp_2306_:
{
lean_object* v___x_2307_; 
lean_inc_ref(v_params_2304_);
lean_inc(v_ctorName_2303_);
lean_inc(v_fvarId_2276_);
v___x_2307_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2276_, v_ctorName_2303_, v_params_2304_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
lean_inc_ref(v___y_2284_);
lean_inc_ref(v_code_2305_);
v___x_2309_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2305_, v___y_2279_, v___y_2280_, v_a_2308_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v_a_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
lean_inc_ref(v_a_2290_);
v___x_2311_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2290_, v_a_2310_);
v_a_2292_ = v___x_2311_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2312_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2309_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2309_);
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
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2320_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2307_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2307_);
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
v___jp_2329_:
{
if (lean_obj_tag(v_code_2305_) == 6)
{
goto v___jp_2306_;
}
else
{
if (v_a_2330_ == 0)
{
goto v___jp_2306_;
}
else
{
lean_object* v___x_2331_; 
lean_inc_ref(v_code_2305_);
v___x_2331_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2328_, v_code_2305_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2328_, v_code_2305_, v___y_2283_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2334_; 
lean_dec_ref_known(v___x_2333_, 1);
v___x_2334_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2280_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec_ref_known(v___x_2334_, 1);
v___x_2335_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2335_, 0, v_a_2332_);
lean_inc_ref(v_a_2290_);
v___x_2336_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2290_, v___x_2335_);
v_a_2292_ = v___x_2336_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2332_);
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
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
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2332_);
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2345_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2333_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2333_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2353_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2331_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2331_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2377_; lean_object* v___x_2378_; 
v_code_2377_ = lean_ctor_get(v_a_2290_, 0);
lean_inc_ref(v___y_2284_);
lean_inc_ref(v_code_2377_);
v___x_2378_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2377_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
lean_inc_ref(v_a_2290_);
v___x_2380_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2290_, v_a_2379_);
v_a_2292_ = v___x_2380_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_as_2278_);
lean_dec(v_i_2277_);
lean_dec(v_fvarId_2276_);
v_a_2381_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2378_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2378_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
v___jp_2291_:
{
size_t v___x_2293_; size_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_ptr_addr(v_a_2290_);
v___x_2294_ = lean_ptr_addr(v_a_2292_);
v___x_2295_ = lean_usize_dec_eq(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v_i_2277_, v___x_2296_);
v___x_2298_ = lean_array_fset(v_as_2278_, v_i_2277_, v_a_2292_);
lean_dec(v_i_2277_);
v_i_2277_ = v___x_2297_;
v_as_2278_ = v___x_2298_;
goto _start;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_a_2292_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_nat_add(v_i_2277_, v___x_2300_);
lean_dec(v_i_2277_);
v_i_2277_ = v___x_2301_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2276_ = stack[0].m_obj;
lean_object* v_i_2277_ = stack[1].m_obj;
lean_object* v_as_2278_ = stack[2].m_obj;
lean_object* v___y_2279_ = stack[3].m_obj;
lean_object* v___y_2280_ = stack[4].m_obj;
lean_object* v___y_2281_ = stack[5].m_obj;
lean_object* v___y_2282_ = stack[6].m_obj;
lean_object* v___y_2283_ = stack[7].m_obj;
lean_object* v___y_2284_ = stack[8].m_obj;
lean_object* v___y_2285_ = stack[9].m_obj;
lean_object* v_res_2389_;
v_res_2389_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_2276_, v_i_2277_, v_as_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
stack->m_obj
 = v_res_2389_;
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2465_; lean_object* v___y_2466_; lean_object* v_decl_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v_decl_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v_decl_2537_; lean_object* v_k_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; lean_object* v_decl_2818_; lean_object* v_fvarId_2819_; lean_object* v_type_2820_; lean_object* v_value_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2910_; lean_object* v___y_2911_; uint8_t v___y_2912_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v_toCold_3314_; lean_object* v_currRecDepth_3315_; lean_object* v_ref_3316_; uint16_t v_optionFlags_3317_; uint8_t v_suppressElabErrors_3318_; uint8_t v_isRecordingDeps_3319_; lean_object* v_maxRecDepth_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_toCold_3314_ = lean_ctor_get(v_a_2397_, 0);
v_currRecDepth_3315_ = lean_ctor_get(v_a_2397_, 1);
v_ref_3316_ = lean_ctor_get(v_a_2397_, 2);
v_optionFlags_3317_ = lean_ctor_get_uint16(v_a_2397_, sizeof(void*)*3);
v_suppressElabErrors_3318_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3319_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*3 + 3);
v_maxRecDepth_3349_ = lean_ctor_get(v_toCold_3314_, 3);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_nat_dec_eq(v_maxRecDepth_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_nat_dec_eq(v_currRecDepth_3315_, v_maxRecDepth_3349_);
if (v___x_3352_ == 0)
{
lean_inc(v_ref_3316_);
lean_inc(v_currRecDepth_3315_);
lean_inc_ref(v_toCold_3314_);
lean_dec_ref(v_a_2397_);
goto v___jp_3320_;
}
else
{
lean_object* v___x_3353_; 
lean_dec_ref(v_code_2391_);
v___x_3353_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec_ref(v_a_2397_);
return v___x_3353_;
}
}
else
{
lean_inc(v_ref_3316_);
lean_inc(v_currRecDepth_3315_);
lean_inc_ref(v_toCold_3314_);
lean_dec_ref(v_a_2397_);
goto v___jp_3320_;
}
v___jp_2400_:
{
switch(lean_obj_tag(v_code_2391_))
{
case 1:
{
lean_object* v_decl_2403_; lean_object* v_k_2404_; size_t v___x_2405_; size_t v___x_2406_; uint8_t v___x_2407_; 
v_decl_2403_ = lean_ctor_get(v_code_2391_, 0);
v_k_2404_ = lean_ctor_get(v_code_2391_, 1);
v___x_2405_ = lean_ptr_addr(v_k_2404_);
v___x_2406_ = lean_ptr_addr(v___y_2401_);
v___x_2407_ = lean_usize_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
v_isSharedCheck_2415_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2416_ = lean_ctor_get(v_code_2391_, 1);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_2417_);
v___x_2409_ = v_code_2391_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v_code_2391_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___y_2401_);
lean_ctor_set(v___x_2409_, 0, v___y_2402_);
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___y_2402_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___y_2401_);
v___x_2412_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
else
{
size_t v___x_2418_; size_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = lean_ptr_addr(v_decl_2403_);
v___x_2419_ = lean_ptr_addr(v___y_2402_);
v___x_2420_ = lean_usize_dec_eq(v___x_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
v_isSharedCheck_2428_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; lean_object* v_unused_2430_; 
v_unused_2429_ = lean_ctor_get(v_code_2391_, 1);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_2430_);
v___x_2422_ = v_code_2391_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_dec(v_code_2391_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___y_2401_);
lean_ctor_set(v___x_2422_, 0, v___y_2402_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___y_2402_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___y_2401_);
v___x_2425_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_code_2391_);
return v___x_2431_;
}
}
}
case 2:
{
lean_object* v_decl_2432_; lean_object* v_k_2433_; size_t v___x_2434_; size_t v___x_2435_; uint8_t v___x_2436_; 
v_decl_2432_ = lean_ctor_get(v_code_2391_, 0);
v_k_2433_ = lean_ctor_get(v_code_2391_, 1);
v___x_2434_ = lean_ptr_addr(v_k_2433_);
v___x_2435_ = lean_ptr_addr(v___y_2401_);
v___x_2436_ = lean_usize_dec_eq(v___x_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; lean_object* v_unused_2446_; 
v_unused_2445_ = lean_ctor_get(v_code_2391_, 1);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_2446_);
v___x_2438_ = v_code_2391_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v_code_2391_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 1, v___y_2401_);
lean_ctor_set(v___x_2438_, 0, v___y_2402_);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___y_2402_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___y_2401_);
v___x_2441_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
else
{
size_t v___x_2447_; size_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2447_ = lean_ptr_addr(v_decl_2432_);
v___x_2448_ = lean_ptr_addr(v___y_2402_);
v___x_2449_ = lean_usize_dec_eq(v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
v_isSharedCheck_2457_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; lean_object* v_unused_2459_; 
v_unused_2458_ = lean_ctor_get(v_code_2391_, 1);
lean_dec(v_unused_2458_);
v_unused_2459_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_2459_);
v___x_2451_ = v_code_2391_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_dec(v_code_2391_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___y_2401_);
lean_ctor_set(v___x_2451_, 0, v___y_2402_);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___y_2402_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___y_2401_);
v___x_2454_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
}
}
else
{
lean_object* v___x_2460_; 
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_code_2391_);
return v___x_2460_;
}
}
}
default: 
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v_code_2391_);
v___x_2461_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2462_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2461_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
}
}
v___jp_2464_:
{
lean_object* v___x_2475_; 
lean_inc_ref(v___y_2473_);
v___x_2475_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2466_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v_fvarId_2477_; lean_object* v___x_2478_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v_fvarId_2477_ = lean_ctor_get(v_decl_2467_, 0);
v___x_2478_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2477_, v___y_2469_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; uint8_t v___x_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2480_ = lean_unbox(v_a_2479_);
lean_dec(v_a_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_code_2391_);
v___x_2481_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2467_, v___y_2469_, v___y_2472_);
lean_dec_ref(v_decl_2467_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v___x_2481_, 0);
lean_dec(v_unused_2489_);
v___x_2483_ = v___x_2481_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_dec(v___x_2481_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v_a_2476_);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2476_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_a_2476_);
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2481_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
if (v___y_2465_ == 0)
{
lean_dec_ref(v___y_2473_);
v___y_2401_ = v_a_2476_;
v___y_2402_ = v_decl_2467_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2498_; 
lean_inc_ref(v_decl_2467_);
v___x_2498_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec_ref(v___y_2473_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_dec_ref_known(v___x_2498_, 1);
v___y_2401_ = v_a_2476_;
v___y_2402_ = v_decl_2467_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_a_2476_);
lean_dec_ref(v_decl_2467_);
lean_dec_ref(v_code_2391_);
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_a_2476_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_decl_2467_);
lean_dec_ref(v_code_2391_);
v_a_2507_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2478_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2478_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_decl_2467_);
lean_dec_ref(v_code_2391_);
return v___x_2475_;
}
}
v___jp_2515_:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___y_2465_ = v___y_2516_;
v___y_2466_ = v___y_2517_;
v_decl_2467_ = v_a_2527_;
v___y_2468_ = v___y_2519_;
v___y_2469_ = v___y_2520_;
v___y_2470_ = v___y_2521_;
v___y_2471_ = v___y_2522_;
v___y_2472_ = v___y_2523_;
v___y_2473_ = v___y_2524_;
v___y_2474_ = v___y_2525_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v_code_2391_);
v_a_2528_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2526_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2526_);
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
v___jp_2536_:
{
lean_object* v_fvarId_2546_; lean_object* v_params_2547_; lean_object* v_type_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; 
v_fvarId_2546_ = lean_ctor_get(v_decl_2537_, 0);
v_params_2547_ = lean_ctor_get(v_decl_2537_, 2);
v_type_2548_ = lean_ctor_get(v_decl_2537_, 3);
v___x_2549_ = 0;
v___x_2550_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2546_, v___y_2540_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; uint8_t v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = lean_unbox(v_a_2551_);
if (v___x_2552_ == 0)
{
uint8_t v___x_2553_; 
v___x_2553_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2391_);
if (v___x_2553_ == 0)
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
v___y_2516_ = v___x_2554_;
v___y_2517_ = v_k_2538_;
v_decl_2518_ = v_decl_2537_;
v___y_2519_ = v___y_2539_;
v___y_2520_ = v___y_2540_;
v___y_2521_ = v___y_2541_;
v___y_2522_ = v___y_2542_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
goto v___jp_2515_;
}
else
{
uint8_t v___x_2555_; 
lean_inc_ref(v_type_2548_);
v___x_2555_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2548_, v_params_2547_);
if (v___x_2555_ == 0)
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
v___y_2516_ = v___x_2556_;
v___y_2517_ = v_k_2538_;
v_decl_2518_ = v_decl_2537_;
v___y_2519_ = v___y_2539_;
v___y_2520_ = v___y_2540_;
v___y_2521_ = v___y_2541_;
v___y_2522_ = v___y_2542_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2557_; lean_object* v_subst_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2557_ = lean_st_ref_get(v___y_2540_);
v_subst_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref(v_subst_2558_);
lean_dec(v___x_2557_);
v___x_2559_ = lean_unbox(v_a_2551_);
v___x_2560_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2549_, v___x_2559_, v_decl_2537_, v_subst_2558_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec_ref(v_subst_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2561_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2540_);
if (lean_obj_tag(v___x_2564_) == 0)
{
uint8_t v___x_2565_; 
lean_dec_ref_known(v___x_2564_, 1);
v___x_2565_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
v___y_2516_ = v___x_2565_;
v___y_2517_ = v_k_2538_;
v_decl_2518_ = v_a_2563_;
v___y_2519_ = v___y_2539_;
v___y_2520_ = v___y_2540_;
v___y_2521_ = v___y_2541_;
v___y_2522_ = v___y_2542_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
goto v___jp_2515_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2563_);
lean_dec(v_a_2551_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_code_2391_);
v_a_2566_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2564_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2564_);
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
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2551_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_code_2391_);
v_a_2574_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2562_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2562_);
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
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_a_2551_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_code_2391_);
v_a_2582_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2560_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2560_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
}
else
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v_subst_2592_; lean_object* v___x_2593_; 
v___x_2590_ = 0;
v___x_2591_ = lean_st_ref_get(v___y_2540_);
v_subst_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref(v_subst_2592_);
lean_dec(v___x_2591_);
v___x_2593_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2549_, v___x_2590_, v_decl_2537_, v_subst_2592_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec_ref(v_subst_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; uint8_t v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
v___y_2465_ = v___x_2595_;
v___y_2466_ = v_k_2538_;
v_decl_2467_ = v_a_2594_;
v___y_2468_ = v___y_2539_;
v___y_2469_ = v___y_2540_;
v___y_2470_ = v___y_2541_;
v___y_2471_ = v___y_2542_;
v___y_2472_ = v___y_2543_;
v___y_2473_ = v___y_2544_;
v___y_2474_ = v___y_2545_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2551_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_code_2391_);
v_a_2596_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2593_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2593_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_k_2538_);
lean_dec_ref(v_decl_2537_);
lean_dec_ref(v_code_2391_);
v_a_2604_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2550_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2550_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
v___jp_2612_:
{
lean_object* v___x_2623_; 
lean_inc_ref(v___y_2622_);
v___x_2623_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2622_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
if (lean_obj_tag(v_a_2624_) == 1)
{
lean_object* v_val_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_val_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_a_2624_, 1);
v___x_2626_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2615_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2626_, 1);
lean_inc_ref(v___y_2618_);
v___x_2627_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2617_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2625_, v_a_2628_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
lean_dec_ref(v___y_2618_);
lean_dec(v_val_2625_);
return v___x_2629_;
}
else
{
lean_dec(v_val_2625_);
lean_dec_ref(v___y_2618_);
return v___x_2627_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_val_2625_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
v_a_2630_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2626_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v___x_2638_; 
lean_dec(v_a_2624_);
lean_inc_ref(v___y_2622_);
v___x_2638_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2622_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
if (lean_obj_tag(v_a_2639_) == 1)
{
lean_object* v_val_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_val_2640_ = lean_ctor_get(v_a_2639_, 0);
lean_inc(v_val_2640_);
lean_dec_ref_known(v_a_2639_, 1);
v___x_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2641_, 0, v_val_2640_);
lean_ctor_set(v___x_2641_, 1, v___y_2617_);
v_code_2391_ = v___x_2641_;
v_a_2392_ = v___y_2614_;
v_a_2393_ = v___y_2615_;
v_a_2394_ = v___y_2621_;
v_a_2395_ = v___y_2616_;
v_a_2396_ = v___y_2619_;
v_a_2397_ = v___y_2618_;
v_a_2398_ = v___y_2620_;
goto _start;
}
else
{
lean_object* v_fvarId_2643_; lean_object* v_value_2644_; lean_object* v___x_2645_; 
lean_dec(v_a_2639_);
v_fvarId_2643_ = lean_ctor_get(v___y_2622_, 0);
v_value_2644_ = lean_ctor_get(v___y_2622_, 3);
v___x_2645_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2644_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
if (lean_obj_tag(v_a_2646_) == 1)
{
lean_object* v_val_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_val_2647_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v_a_2646_, 1);
lean_inc(v_fvarId_2643_);
v___x_2648_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2643_, v_val_2647_, v___y_2615_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2648_, 1);
v___x_2649_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2622_, v___y_2615_, v___y_2619_);
lean_dec_ref(v___y_2622_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_dec_ref_known(v___x_2649_, 1);
v_code_2391_ = v___y_2617_;
v_a_2392_ = v___y_2614_;
v_a_2393_ = v___y_2615_;
v_a_2394_ = v___y_2621_;
v_a_2395_ = v___y_2616_;
v_a_2396_ = v___y_2619_;
v_a_2397_ = v___y_2618_;
v_a_2398_ = v___y_2620_;
goto _start;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
v_a_2651_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2649_);
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
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
v_a_2659_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2648_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2648_);
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
lean_object* v___x_2667_; 
lean_dec(v_a_2646_);
lean_inc_ref(v___y_2617_);
lean_inc_ref(v___y_2622_);
v___x_2667_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2622_, v___y_2617_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
if (lean_obj_tag(v_a_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_val_2669_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_a_2668_, 1);
v___x_2670_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2622_, v___y_2615_, v___y_2619_);
lean_dec_ref(v___y_2622_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v___x_2670_, 0);
lean_dec(v_unused_2678_);
v___x_2672_ = v___x_2670_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v___x_2670_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v_val_2669_);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_val_2669_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_val_2669_);
v_a_2679_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2670_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2670_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_a_2668_);
lean_inc(v_value_2644_);
v___x_2687_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2644_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
if (lean_obj_tag(v_a_2688_) == 1)
{
lean_object* v_val_2689_; lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2692_; 
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_val_2689_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v_a_2688_, 1);
v_fst_2690_ = lean_ctor_get(v_val_2689_, 0);
lean_inc(v_fst_2690_);
v_snd_2691_ = lean_ctor_get(v_val_2689_, 1);
lean_inc(v_snd_2691_);
lean_dec(v_val_2689_);
lean_inc(v_fvarId_2643_);
v___x_2692_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2643_, v_snd_2691_, v___y_2615_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2693_; 
lean_dec_ref_known(v___x_2692_, 1);
v___x_2693_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2622_, v___y_2615_, v___y_2619_);
lean_dec_ref(v___y_2622_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2694_; 
lean_dec_ref_known(v___x_2693_, 1);
lean_inc_ref(v___y_2618_);
v___x_2694_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2617_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2690_, v_a_2695_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
lean_dec_ref(v___y_2618_);
lean_dec(v_fst_2690_);
return v___x_2696_;
}
else
{
lean_dec(v_fst_2690_);
lean_dec_ref(v___y_2618_);
return v___x_2694_;
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_fst_2690_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
v_a_2697_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2693_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2693_);
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
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_fst_2690_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
v_a_2705_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2692_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2692_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; 
lean_dec(v_a_2688_);
lean_inc_ref(v___y_2618_);
lean_inc_ref(v___y_2617_);
v___x_2713_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2617_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2643_, v___y_2615_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; uint8_t v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = lean_unbox(v_a_2716_);
lean_dec(v_a_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v___x_2718_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2622_, v___y_2615_, v___y_2619_);
lean_dec_ref(v___y_2622_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2718_, 0);
lean_dec(v_unused_2726_);
v___x_2720_ = v___x_2718_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v___x_2718_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v_a_2714_);
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2714_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2714_);
v_a_2727_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2718_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2718_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v___x_2735_; 
lean_inc_ref(v___y_2622_);
v___x_2735_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2622_, v___y_2614_, v___y_2615_, v___y_2621_, v___y_2616_, v___y_2619_, v___y_2618_, v___y_2620_);
lean_dec_ref(v___y_2618_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2756_; 
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; 
v_unused_2757_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2757_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2756_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2756_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
size_t v___x_2739_; size_t v___x_2740_; uint8_t v___x_2741_; 
v___x_2739_ = lean_ptr_addr(v___y_2617_);
lean_dec_ref(v___y_2617_);
v___x_2740_ = lean_ptr_addr(v_a_2714_);
v___x_2741_ = lean_usize_dec_eq(v___x_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2622_);
lean_ctor_set(v___x_2742_, 1, v_a_2714_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2742_);
v___x_2744_ = v___x_2737_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
else
{
size_t v___x_2746_; size_t v___x_2747_; uint8_t v___x_2748_; 
v___x_2746_ = lean_ptr_addr(v___y_2613_);
lean_dec_ref(v___y_2613_);
v___x_2747_ = lean_ptr_addr(v___y_2622_);
v___x_2748_ = lean_usize_dec_eq(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec_ref(v_code_2391_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___y_2622_);
lean_ctor_set(v___x_2749_, 1, v_a_2714_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2749_);
v___x_2751_ = v___x_2737_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v_a_2714_);
lean_dec_ref(v___y_2622_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v_code_2391_);
v___x_2754_ = v___x_2737_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_code_2391_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2714_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2758_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2735_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2735_);
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
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2714_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2766_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2715_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2715_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
return v___x_2713_;
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2774_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2687_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2687_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2782_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2667_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2667_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2790_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2645_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2645_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2798_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2638_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2638_);
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
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_code_2391_);
v_a_2806_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2623_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2623_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
v___jp_2814_:
{
uint8_t v___x_2829_; 
v___x_2829_ = l_Lean_Expr_isErased(v_type_2820_);
lean_dec_ref(v_type_2820_);
if (v___x_2829_ == 0)
{
lean_dec(v_value_2821_);
lean_dec(v_fvarId_2819_);
v___y_2613_ = v___y_2815_;
v___y_2614_ = v___y_2822_;
v___y_2615_ = v___y_2823_;
v___y_2616_ = v___y_2825_;
v___y_2617_ = v___y_2816_;
v___y_2618_ = v___y_2827_;
v___y_2619_ = v___y_2826_;
v___y_2620_ = v___y_2828_;
v___y_2621_ = v___y_2824_;
v___y_2622_ = v_decl_2818_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = lean_box(1);
v___x_2831_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2817_, v_value_2821_, v___x_2830_);
lean_dec(v_value_2821_);
if (v___x_2831_ == 0)
{
if (v___x_2829_ == 0)
{
lean_dec(v_fvarId_2819_);
v___y_2613_ = v___y_2815_;
v___y_2614_ = v___y_2822_;
v___y_2615_ = v___y_2823_;
v___y_2616_ = v___y_2825_;
v___y_2617_ = v___y_2816_;
v___y_2618_ = v___y_2827_;
v___y_2619_ = v___y_2826_;
v___y_2620_ = v___y_2828_;
v___y_2621_ = v___y_2824_;
v___y_2622_ = v_decl_2818_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v_subst_2834_; lean_object* v_used_2835_; lean_object* v_binderRenaming_2836_; lean_object* v_funDeclInfoMap_2837_; uint8_t v_simplified_2838_; lean_object* v_visited_2839_; lean_object* v_inline_2840_; lean_object* v_inlineLocal_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v___y_2815_);
lean_dec_ref(v_code_2391_);
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_st_ref_take(v___y_2823_);
v_subst_2834_ = lean_ctor_get(v___x_2833_, 0);
v_used_2835_ = lean_ctor_get(v___x_2833_, 1);
v_binderRenaming_2836_ = lean_ctor_get(v___x_2833_, 2);
v_funDeclInfoMap_2837_ = lean_ctor_get(v___x_2833_, 3);
v_simplified_2838_ = lean_ctor_get_uint8(v___x_2833_, sizeof(void*)*7);
v_visited_2839_ = lean_ctor_get(v___x_2833_, 4);
v_inline_2840_ = lean_ctor_get(v___x_2833_, 5);
v_inlineLocal_2841_ = lean_ctor_get(v___x_2833_, 6);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2843_ = v___x_2833_;
v_isShared_2844_ = v_isSharedCheck_2860_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_inlineLocal_2841_);
lean_inc(v_inline_2840_);
lean_inc(v_visited_2839_);
lean_inc(v_funDeclInfoMap_2837_);
lean_inc(v_binderRenaming_2836_);
lean_inc(v_used_2835_);
lean_inc(v_subst_2834_);
lean_dec(v___x_2833_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2860_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2834_, v_fvarId_2819_, v___x_2832_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_used_2835_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_binderRenaming_2836_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_funDeclInfoMap_2837_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v_visited_2839_);
lean_ctor_set(v_reuseFailAlloc_2859_, 5, v_inline_2840_);
lean_ctor_set(v_reuseFailAlloc_2859_, 6, v_inlineLocal_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2859_, sizeof(void*)*7, v_simplified_2838_);
v___x_2847_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_st_ref_put(v___y_2823_, v___x_2847_);
v___x_2849_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2818_, v___y_2823_, v___y_2826_);
lean_dec_ref(v_decl_2818_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_dec_ref_known(v___x_2849_, 1);
v_code_2391_ = v___y_2816_;
v_a_2392_ = v___y_2822_;
v_a_2393_ = v___y_2823_;
v_a_2394_ = v___y_2824_;
v_a_2395_ = v___y_2825_;
v_a_2396_ = v___y_2826_;
v_a_2397_ = v___y_2827_;
v_a_2398_ = v___y_2828_;
goto _start;
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v___y_2827_);
lean_dec_ref(v___y_2816_);
v_a_2851_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2849_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2819_);
v___y_2613_ = v___y_2815_;
v___y_2614_ = v___y_2822_;
v___y_2615_ = v___y_2823_;
v___y_2616_ = v___y_2825_;
v___y_2617_ = v___y_2816_;
v___y_2618_ = v___y_2827_;
v___y_2619_ = v___y_2826_;
v___y_2620_ = v___y_2828_;
v___y_2621_ = v___y_2824_;
v___y_2622_ = v_decl_2818_;
goto v___jp_2612_;
}
}
}
v___jp_2861_:
{
lean_object* v_fvarId_2873_; lean_object* v_type_2874_; lean_object* v_value_2875_; lean_object* v___x_2876_; 
v_fvarId_2873_ = lean_ctor_get(v___y_2864_, 0);
v_type_2874_ = lean_ctor_get(v___y_2864_, 2);
v_value_2875_ = lean_ctor_get(v___y_2864_, 3);
lean_inc(v_value_2875_);
v___x_2876_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2875_, v___y_2866_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
if (lean_obj_tag(v_a_2877_) == 1)
{
lean_object* v_val_2878_; lean_object* v___x_2879_; 
v_val_2878_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v_a_2877_, 1);
v___x_2879_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2867_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2880_; 
lean_dec_ref_known(v___x_2879_, 1);
v___x_2880_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2865_, v___y_2864_, v_val_2878_, v___y_2870_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v_fvarId_2882_; lean_object* v_type_2883_; lean_object* v_value_2884_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v_fvarId_2882_ = lean_ctor_get(v_a_2881_, 0);
lean_inc(v_fvarId_2882_);
v_type_2883_ = lean_ctor_get(v_a_2881_, 2);
lean_inc_ref(v_type_2883_);
v_value_2884_ = lean_ctor_get(v_a_2881_, 3);
lean_inc(v_value_2884_);
v___y_2815_ = v___y_2862_;
v___y_2816_ = v___y_2863_;
v___y_2817_ = v___y_2865_;
v_decl_2818_ = v_a_2881_;
v_fvarId_2819_ = v_fvarId_2882_;
v_type_2820_ = v_type_2883_;
v_value_2821_ = v_value_2884_;
v___y_2822_ = v___y_2866_;
v___y_2823_ = v___y_2867_;
v___y_2824_ = v___y_2868_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v___y_2872_;
goto v___jp_2814_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v___y_2871_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_code_2391_);
v_a_2885_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2880_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2880_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_val_2878_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_code_2391_);
v_a_2893_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2879_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2879_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_inc(v_value_2875_);
lean_inc_ref(v_type_2874_);
lean_inc(v_fvarId_2873_);
lean_dec(v_a_2877_);
v___y_2815_ = v___y_2862_;
v___y_2816_ = v___y_2863_;
v___y_2817_ = v___y_2865_;
v_decl_2818_ = v___y_2864_;
v_fvarId_2819_ = v_fvarId_2873_;
v_type_2820_ = v_type_2874_;
v_value_2821_ = v_value_2875_;
v___y_2822_ = v___y_2866_;
v___y_2823_ = v___y_2867_;
v___y_2824_ = v___y_2868_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v___y_2872_;
goto v___jp_2814_;
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___y_2871_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_code_2391_);
v_a_2901_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2876_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2876_);
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
if (v___y_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_dec_ref(v_code_2391_);
v___x_2913_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2910_);
lean_ctor_set(v___x_2913_, 1, v___y_2911_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
else
{
lean_object* v___x_2915_; 
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v_code_2391_);
return v___x_2915_;
}
}
v___jp_2916_:
{
uint8_t v___x_2921_; 
v___x_2921_ = l_Lean_instBEqFVarId_beq(v___y_2917_, v___y_2918_);
lean_dec(v___y_2917_);
if (v___x_2921_ == 0)
{
lean_dec_ref(v___y_2920_);
v___y_2910_ = v___y_2918_;
v___y_2911_ = v___y_2919_;
v___y_2912_ = v___x_2921_;
goto v___jp_2909_;
}
else
{
size_t v___x_2922_; size_t v___x_2923_; uint8_t v___x_2924_; 
v___x_2922_ = lean_ptr_addr(v___y_2920_);
lean_dec_ref(v___y_2920_);
v___x_2923_ = lean_ptr_addr(v___y_2919_);
v___x_2924_ = lean_usize_dec_eq(v___x_2922_, v___x_2923_);
v___y_2910_ = v___y_2918_;
v___y_2911_ = v___y_2919_;
v___y_2912_ = v___x_2924_;
goto v___jp_2909_;
}
}
v___jp_2925_:
{
if (lean_obj_tag(v___y_2930_) == 0)
{
lean_dec_ref_known(v___y_2930_, 1);
v___y_2917_ = v___y_2926_;
v___y_2918_ = v___y_2927_;
v___y_2919_ = v___y_2928_;
v___y_2920_ = v___y_2929_;
goto v___jp_2916_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v_code_2391_);
v_a_2931_ = lean_ctor_get(v___y_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___y_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___y_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___y_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
v___jp_2939_:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2950_; 
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2942_, 0);
lean_dec(v_unused_2951_);
v___x_2944_ = v___x_2942_;
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
else
{
lean_dec(v___x_2942_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2950_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___y_2940_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v___y_2940_);
v_a_2952_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2942_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2960_:
{
if (lean_obj_tag(v___y_2963_) == 0)
{
lean_dec_ref_known(v___y_2963_, 1);
v___y_2940_ = v___y_2961_;
v___y_2941_ = v___y_2962_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v___y_2961_);
v_a_2964_ = lean_ctor_get(v___y_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___y_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___y_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___y_2963_);
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
v___jp_2972_:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_nat_dec_lt(v___y_2974_, v___y_2980_);
lean_dec(v___y_2974_);
if (v___x_2982_ == 0)
{
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2976_);
v___y_2940_ = v___y_2973_;
v___y_2941_ = v___y_2979_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_nat_dec_le(v___y_2980_, v___y_2980_);
if (v___x_2984_ == 0)
{
if (v___x_2982_ == 0)
{
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2976_);
v___y_2940_ = v___y_2973_;
v___y_2941_ = v___y_2979_;
goto v___jp_2939_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___y_2980_);
lean_dec(v___y_2980_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2976_, v___x_2985_, v___x_2986_, v___x_2983_, v___y_2981_, v___y_2975_, v___y_2978_, v___y_2977_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2976_);
v___y_2961_ = v___y_2973_;
v___y_2962_ = v___y_2979_;
v___y_2963_ = v___x_2987_;
goto v___jp_2960_;
}
}
else
{
size_t v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((size_t)0ULL);
v___x_2989_ = lean_usize_of_nat(v___y_2980_);
lean_dec(v___y_2980_);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2976_, v___x_2988_, v___x_2989_, v___x_2983_, v___y_2981_, v___y_2975_, v___y_2978_, v___y_2977_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2976_);
v___y_2961_ = v___y_2973_;
v___y_2962_ = v___y_2979_;
v___y_2963_ = v___x_2990_;
goto v___jp_2960_;
}
}
}
v___jp_2991_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2995_);
lean_ctor_set(v___x_2996_, 1, v___y_2992_);
lean_ctor_set(v___x_2996_, 2, v___y_2993_);
lean_ctor_set(v___x_2996_, 3, v___y_2994_);
v___x_2997_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
v___jp_2999_:
{
lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = lean_array_get_size(v___y_3004_);
v___x_3014_ = lean_nat_dec_lt(v___y_3000_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_code_2391_);
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___y_3000_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3004_;
v___y_2977_ = v___y_3012_;
v___y_2978_ = v___y_3011_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___x_3013_;
v___y_2981_ = v___y_3009_;
goto v___jp_2972_;
}
else
{
if (v___x_3014_ == 0)
{
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_code_2391_);
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___y_3000_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3004_;
v___y_2977_ = v___y_3012_;
v___y_2978_ = v___y_3011_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___x_3013_;
v___y_2981_ = v___y_3009_;
goto v___jp_2972_;
}
else
{
size_t v___x_3015_; size_t v___x_3016_; uint8_t v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3013_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_3004_, v___x_3015_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_code_2391_);
v___y_2973_ = v___y_3001_;
v___y_2974_ = v___y_3000_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3004_;
v___y_2977_ = v___y_3012_;
v___y_2978_ = v___y_3011_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___x_3013_;
v___y_2981_ = v___y_3009_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_3018_; 
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3000_);
lean_inc(v___y_3003_);
v___x_3018_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_3003_, v___y_3008_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3032_; 
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v___x_3018_, 0);
lean_dec(v_unused_3033_);
v___x_3020_ = v___x_3018_;
v_isShared_3021_ = v_isSharedCheck_3032_;
goto v_resetjp_3019_;
}
else
{
lean_dec(v___x_3018_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3032_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
size_t v___x_3022_; size_t v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_ptr_addr(v___y_3002_);
lean_dec_ref(v___y_3002_);
v___x_3023_ = lean_ptr_addr(v___y_3004_);
v___x_3024_ = lean_usize_dec_eq(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_del_object(v___x_3020_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3005_);
lean_dec_ref(v_code_2391_);
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3003_;
v___y_2994_ = v___y_3004_;
v___y_2995_ = v___y_3006_;
goto v___jp_2991_;
}
else
{
size_t v___x_3025_; size_t v___x_3026_; uint8_t v___x_3027_; 
v___x_3025_ = lean_ptr_addr(v___y_3007_);
lean_dec_ref(v___y_3007_);
v___x_3026_ = lean_ptr_addr(v___y_3001_);
v___x_3027_ = lean_usize_dec_eq(v___x_3025_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_del_object(v___x_3020_);
lean_dec(v___y_3005_);
lean_dec_ref(v_code_2391_);
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3003_;
v___y_2994_ = v___y_3004_;
v___y_2995_ = v___y_3006_;
goto v___jp_2991_;
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = l_Lean_instBEqFVarId_beq(v___y_3005_, v___y_3003_);
lean_dec(v___y_3005_);
if (v___x_3028_ == 0)
{
lean_del_object(v___x_3020_);
lean_dec_ref(v_code_2391_);
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3003_;
v___y_2994_ = v___y_3004_;
v___y_2995_ = v___y_3006_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3030_; 
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3001_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_code_2391_);
v___x_3030_ = v___x_3020_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_code_2391_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v_code_2391_);
v_a_3034_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3018_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3018_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
}
v___jp_3042_:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3043_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_3045_, 0);
lean_dec(v_unused_3053_);
v___x_3047_ = v___x_3045_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v___x_3045_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___y_3044_);
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___y_3044_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___y_3044_);
v_a_3054_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3045_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3045_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
v___jp_3062_:
{
if (lean_obj_tag(v___y_3065_) == 0)
{
lean_dec_ref_known(v___y_3065_, 1);
v___y_3043_ = v___y_3063_;
v___y_3044_ = v___y_3064_;
goto v___jp_3042_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___y_3064_);
v_a_3066_ = lean_ctor_get(v___y_3065_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___y_3065_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___y_3065_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___y_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
v___jp_3074_:
{
uint8_t v___x_3081_; 
v___x_3081_ = lean_nat_dec_lt(v___y_3077_, v___y_3080_);
lean_dec(v___y_3077_);
if (v___x_3081_ == 0)
{
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3075_);
v___y_3043_ = v___y_3076_;
v___y_3044_ = v___y_3078_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_nat_dec_le(v___y_3080_, v___y_3080_);
if (v___x_3083_ == 0)
{
if (v___x_3081_ == 0)
{
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3075_);
v___y_3043_ = v___y_3076_;
v___y_3044_ = v___y_3078_;
goto v___jp_3042_;
}
else
{
size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = lean_usize_of_nat(v___y_3080_);
lean_dec(v___y_3080_);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3075_, v___x_3084_, v___x_3085_, v___x_3082_, v___y_3079_);
lean_dec_ref(v___y_3075_);
v___y_3063_ = v___y_3076_;
v___y_3064_ = v___y_3078_;
v___y_3065_ = v___x_3086_;
goto v___jp_3062_;
}
}
else
{
size_t v___x_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = lean_usize_of_nat(v___y_3080_);
lean_dec(v___y_3080_);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3075_, v___x_3087_, v___x_3088_, v___x_3082_, v___y_3079_);
lean_dec_ref(v___y_3075_);
v___y_3063_ = v___y_3076_;
v___y_3064_ = v___y_3078_;
v___y_3065_ = v___x_3089_;
goto v___jp_3062_;
}
}
}
v___jp_3090_:
{
switch(lean_obj_tag(v_code_2391_))
{
case 0:
{
lean_object* v_decl_3098_; lean_object* v_k_3099_; uint8_t v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; 
v_decl_3098_ = lean_ctor_get(v_code_2391_, 0);
v_k_3099_ = lean_ctor_get(v_code_2391_, 1);
v___x_3100_ = 0;
v___x_3101_ = 0;
lean_inc_ref(v_decl_3098_);
v___x_3102_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3100_, v___x_3101_, v_decl_3098_, v___y_3092_, v___y_3095_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; uint8_t v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3100_, v_decl_3098_, v_a_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3092_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref_known(v___x_3105_, 1);
lean_inc_ref(v_k_3099_);
lean_inc_ref(v_decl_3098_);
v___y_2862_ = v_decl_3098_;
v___y_2863_ = v_k_3099_;
v___y_2864_ = v_a_3103_;
v___y_2865_ = v___x_3100_;
v___y_2866_ = v___y_3091_;
v___y_2867_ = v___y_3092_;
v___y_2868_ = v___y_3093_;
v___y_2869_ = v___y_3094_;
v___y_2870_ = v___y_3095_;
v___y_2871_ = v___y_3096_;
v___y_2872_ = v___y_3097_;
goto v___jp_2861_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3103_);
lean_dec_ref_known(v_code_2391_, 2);
lean_dec_ref(v___y_3096_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_inc_ref(v_k_3099_);
lean_inc_ref(v_decl_3098_);
v___y_2862_ = v_decl_3098_;
v___y_2863_ = v_k_3099_;
v___y_2864_ = v_a_3103_;
v___y_2865_ = v___x_3100_;
v___y_2866_ = v___y_3091_;
v___y_2867_ = v___y_3092_;
v___y_2868_ = v___y_3093_;
v___y_2869_ = v___y_3094_;
v___y_2870_ = v___y_3095_;
v___y_2871_ = v___y_3096_;
v___y_2872_ = v___y_3097_;
goto v___jp_2861_;
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref_known(v_code_2391_, 2);
lean_dec_ref(v___y_3096_);
v_a_3114_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3102_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3102_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3122_; lean_object* v_args_3123_; uint8_t v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v_subst_3127_; lean_object* v___x_3128_; 
v_fvarId_3122_ = lean_ctor_get(v_code_2391_, 0);
v_args_3123_ = lean_ctor_get(v_code_2391_, 1);
v___x_3124_ = 0;
v___x_3125_ = 0;
v___x_3126_ = lean_st_ref_get(v___y_3092_);
v_subst_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_subst_3127_);
lean_dec(v___x_3126_);
lean_inc(v_fvarId_3122_);
v___x_3128_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3127_, v_fvarId_3122_, v___x_3125_);
lean_dec_ref(v_subst_3127_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_fvarId_3129_; lean_object* v___x_3130_; 
v_fvarId_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_fvarId_3129_);
lean_dec_ref_known(v___x_3128_, 1);
lean_inc_ref(v_args_3123_);
v___x_3130_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3124_, v___x_3125_, v_args_3123_, v___y_3092_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc_n(v_a_3131_, 2);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3129_, v_a_3131_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
if (lean_obj_tag(v_a_3133_) == 1)
{
lean_object* v_val_3134_; 
lean_dec(v_a_3131_);
lean_dec(v_fvarId_3129_);
lean_dec_ref_known(v_code_2391_, 2);
v_val_3134_ = lean_ctor_get(v_a_3133_, 0);
lean_inc(v_val_3134_);
lean_dec_ref_known(v_a_3133_, 1);
v_code_2391_ = v_val_3134_;
v_a_2392_ = v___y_3091_;
v_a_2393_ = v___y_3092_;
v_a_2394_ = v___y_3093_;
v_a_2395_ = v___y_3094_;
v_a_2396_ = v___y_3095_;
v_a_2397_ = v___y_3096_;
v_a_2398_ = v___y_3097_;
goto _start;
}
else
{
lean_object* v___x_3136_; 
lean_dec(v_a_3133_);
lean_dec_ref(v___y_3096_);
lean_inc(v_fvarId_3129_);
v___x_3136_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3129_, v___y_3092_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
lean_dec_ref_known(v___x_3136_, 1);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_array_get_size(v_a_3131_);
v___x_3139_ = lean_nat_dec_lt(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_inc_ref(v_args_3123_);
lean_inc(v_fvarId_3122_);
v___y_2917_ = v_fvarId_3122_;
v___y_2918_ = v_fvarId_3129_;
v___y_2919_ = v_a_3131_;
v___y_2920_ = v_args_3123_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = lean_box(0);
v___x_3141_ = lean_nat_dec_le(v___x_3138_, v___x_3138_);
if (v___x_3141_ == 0)
{
if (v___x_3139_ == 0)
{
lean_inc_ref(v_args_3123_);
lean_inc(v_fvarId_3122_);
v___y_2917_ = v_fvarId_3122_;
v___y_2918_ = v_fvarId_3129_;
v___y_2919_ = v_a_3131_;
v___y_2920_ = v_args_3123_;
goto v___jp_2916_;
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = lean_usize_of_nat(v___x_3138_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3131_, v___x_3142_, v___x_3143_, v___x_3140_, v___y_3092_);
lean_inc_ref(v_args_3123_);
lean_inc(v_fvarId_3122_);
v___y_2926_ = v_fvarId_3122_;
v___y_2927_ = v_fvarId_3129_;
v___y_2928_ = v_a_3131_;
v___y_2929_ = v_args_3123_;
v___y_2930_ = v___x_3144_;
goto v___jp_2925_;
}
}
else
{
size_t v___x_3145_; size_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = ((size_t)0ULL);
v___x_3146_ = lean_usize_of_nat(v___x_3138_);
v___x_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3131_, v___x_3145_, v___x_3146_, v___x_3140_, v___y_3092_);
lean_inc_ref(v_args_3123_);
lean_inc(v_fvarId_3122_);
v___y_2926_ = v_fvarId_3122_;
v___y_2927_ = v_fvarId_3129_;
v___y_2928_ = v_a_3131_;
v___y_2929_ = v_args_3123_;
v___y_2930_ = v___x_3147_;
goto v___jp_2925_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_3131_);
lean_dec(v_fvarId_3129_);
lean_dec_ref_known(v_code_2391_, 2);
v_a_3148_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3136_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3136_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_a_3131_);
lean_dec(v_fvarId_3129_);
lean_dec_ref_known(v_code_2391_, 2);
lean_dec_ref(v___y_3096_);
v_a_3156_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3132_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3132_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_fvarId_3129_);
lean_dec_ref_known(v_code_2391_, 2);
lean_dec_ref(v___y_3096_);
v_a_3164_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3130_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3130_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v___x_3172_; 
lean_dec_ref_known(v_code_2391_, 2);
v___x_3172_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3124_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec_ref(v___y_3096_);
return v___x_3172_;
}
}
case 4:
{
lean_object* v_cases_3173_; lean_object* v___x_3174_; 
v_cases_3173_ = lean_ctor_get(v_code_2391_, 0);
lean_inc_ref(v_cases_3173_);
v___x_3174_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3173_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3247_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3247_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3247_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
if (lean_obj_tag(v_a_3175_) == 1)
{
lean_object* v_val_3179_; lean_object* v___x_3181_; 
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_val_3179_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_val_3179_);
lean_dec_ref_known(v_a_3175_, 1);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v_val_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_val_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
else
{
lean_object* v_typeName_3183_; lean_object* v_resultType_3184_; lean_object* v_discr_3185_; lean_object* v_alts_3186_; uint8_t v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v_subst_3190_; lean_object* v___x_3191_; 
lean_del_object(v___x_3177_);
lean_dec(v_a_3175_);
v_typeName_3183_ = lean_ctor_get(v_cases_3173_, 0);
v_resultType_3184_ = lean_ctor_get(v_cases_3173_, 1);
v_discr_3185_ = lean_ctor_get(v_cases_3173_, 2);
v_alts_3186_ = lean_ctor_get(v_cases_3173_, 3);
v___x_3187_ = 0;
v___x_3188_ = 0;
v___x_3189_ = lean_st_ref_get(v___y_3092_);
v_subst_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc_ref(v_subst_3190_);
lean_dec(v___x_3189_);
lean_inc(v_discr_3185_);
v___x_3191_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3190_, v_discr_3185_, v___x_3188_);
lean_dec_ref(v_subst_3190_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_fvarId_3192_; lean_object* v___x_3193_; lean_object* v_subst_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_fvarId_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc_n(v_fvarId_3192_, 2);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = lean_st_ref_get(v___y_3092_);
v_subst_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc_ref(v_subst_3194_);
lean_dec(v___x_3193_);
lean_inc_ref(v_resultType_3184_);
v___x_3195_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3187_, v_subst_3194_, v___x_3188_, v_resultType_3184_);
lean_dec_ref(v_subst_3194_);
v___x_3196_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3186_);
v___x_3197_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3192_, v___x_3196_, v_alts_3186_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3198_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3229_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3229_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3229_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v___x_3204_ = lean_array_get_size(v_a_3200_);
v___x_3205_ = lean_unsigned_to_nat(1u);
v___x_3206_ = lean_nat_dec_eq(v___x_3204_, v___x_3205_);
if (v___x_3206_ == 0)
{
lean_del_object(v___x_3202_);
lean_inc_ref(v_resultType_3184_);
lean_inc(v_typeName_3183_);
lean_inc(v_discr_3185_);
lean_inc_ref(v_alts_3186_);
v___y_3000_ = v___x_3196_;
v___y_3001_ = v___x_3195_;
v___y_3002_ = v_alts_3186_;
v___y_3003_ = v_fvarId_3192_;
v___y_3004_ = v_a_3200_;
v___y_3005_ = v_discr_3185_;
v___y_3006_ = v_typeName_3183_;
v___y_3007_ = v_resultType_3184_;
v___y_3008_ = v___y_3092_;
v___y_3009_ = v___y_3094_;
v___y_3010_ = v___y_3095_;
v___y_3011_ = v___y_3096_;
v___y_3012_ = v___y_3097_;
goto v___jp_2999_;
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_array_fget_borrowed(v_a_3200_, v___x_3196_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_params_3208_; lean_object* v_code_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
lean_del_object(v___x_3202_);
v_params_3208_ = lean_ctor_get(v___x_3207_, 1);
v_code_3209_ = lean_ctor_get(v___x_3207_, 2);
v___x_3210_ = lean_array_get_size(v_params_3208_);
v___x_3211_ = lean_nat_dec_lt(v___x_3196_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_inc_ref(v_code_3209_);
lean_inc_ref(v_params_3208_);
lean_dec(v_a_3200_);
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v___y_3075_ = v_params_3208_;
v___y_3076_ = v___y_3092_;
v___y_3077_ = v___x_3196_;
v___y_3078_ = v_code_3209_;
v___y_3079_ = v___y_3095_;
v___y_3080_ = v___x_3210_;
goto v___jp_3074_;
}
else
{
if (v___x_3211_ == 0)
{
lean_inc_ref(v_code_3209_);
lean_inc_ref(v_params_3208_);
lean_dec(v_a_3200_);
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v___y_3075_ = v_params_3208_;
v___y_3076_ = v___y_3092_;
v___y_3077_ = v___x_3196_;
v___y_3078_ = v_code_3209_;
v___y_3079_ = v___y_3095_;
v___y_3080_ = v___x_3210_;
goto v___jp_3074_;
}
else
{
size_t v___x_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = ((size_t)0ULL);
v___x_3213_ = lean_usize_of_nat(v___x_3210_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3208_, v___x_3212_, v___x_3213_, v___y_3092_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; uint8_t v___x_3216_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = lean_unbox(v_a_3215_);
lean_dec(v_a_3215_);
if (v___x_3216_ == 0)
{
lean_inc_ref(v_code_3209_);
lean_inc_ref(v_params_3208_);
lean_dec(v_a_3200_);
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v___y_3075_ = v_params_3208_;
v___y_3076_ = v___y_3092_;
v___y_3077_ = v___x_3196_;
v___y_3078_ = v_code_3209_;
v___y_3079_ = v___y_3095_;
v___y_3080_ = v___x_3210_;
goto v___jp_3074_;
}
else
{
lean_inc_ref(v_resultType_3184_);
lean_inc(v_typeName_3183_);
lean_inc(v_discr_3185_);
lean_inc_ref(v_alts_3186_);
v___y_3000_ = v___x_3196_;
v___y_3001_ = v___x_3195_;
v___y_3002_ = v_alts_3186_;
v___y_3003_ = v_fvarId_3192_;
v___y_3004_ = v_a_3200_;
v___y_3005_ = v_discr_3185_;
v___y_3006_ = v_typeName_3183_;
v___y_3007_ = v_resultType_3184_;
v___y_3008_ = v___y_3092_;
v___y_3009_ = v___y_3094_;
v___y_3010_ = v___y_3095_;
v___y_3011_ = v___y_3096_;
v___y_3012_ = v___y_3097_;
goto v___jp_2999_;
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3200_);
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_a_3217_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3214_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3214_);
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
}
}
else
{
lean_object* v_code_3225_; lean_object* v___x_3227_; 
lean_inc_ref(v___x_3207_);
lean_dec(v_a_3200_);
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_code_3225_ = lean_ctor_get(v___x_3207_, 0);
lean_inc_ref(v_code_3225_);
lean_dec_ref_known(v___x_3207_, 1);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v_code_3225_);
v___x_3227_ = v___x_3202_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_code_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_a_3230_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3199_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3199_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v___x_3195_);
lean_dec(v_fvarId_3192_);
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_a_3238_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3197_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3197_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
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
lean_object* v___x_3246_; 
lean_dec_ref_known(v_code_2391_, 1);
v___x_3246_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3187_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec_ref(v___y_3096_);
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref_known(v_code_2391_, 1);
lean_dec_ref(v___y_3096_);
v_a_3248_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3174_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3174_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3256_; uint8_t v___x_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v_subst_3260_; lean_object* v___x_3261_; 
v_fvarId_3256_ = lean_ctor_get(v_code_2391_, 0);
v___x_3257_ = 0;
v___x_3258_ = 0;
v___x_3259_ = lean_st_ref_get(v___y_3092_);
v_subst_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_subst_3260_);
lean_dec(v___x_3259_);
lean_inc(v_fvarId_3256_);
v___x_3261_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3260_, v_fvarId_3256_, v___x_3258_);
lean_dec_ref(v_subst_3260_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_fvarId_3262_; lean_object* v___x_3263_; 
lean_dec_ref(v___y_3096_);
v_fvarId_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_n(v_fvarId_3262_, 2);
lean_dec_ref_known(v___x_3261_, 1);
v___x_3263_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3262_, v___y_3092_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3282_; 
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v___x_3263_, 0);
lean_dec(v_unused_3283_);
v___x_3265_ = v___x_3263_;
v_isShared_3266_ = v_isSharedCheck_3282_;
goto v_resetjp_3264_;
}
else
{
lean_dec(v___x_3263_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3282_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_instBEqFVarId_beq(v_fvarId_3256_, v_fvarId_3262_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3277_; 
v_isSharedCheck_3277_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_3278_);
v___x_3269_ = v_code_2391_;
v_isShared_3270_ = v_isSharedCheck_3277_;
goto v_resetjp_3268_;
}
else
{
lean_dec(v_code_2391_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3277_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v_fvarId_3262_);
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_fvarId_3262_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3272_);
v___x_3274_ = v___x_3265_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v___x_3280_; 
lean_dec(v_fvarId_3262_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_code_2391_);
v___x_3280_ = v___x_3265_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_code_2391_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_fvarId_3262_);
lean_dec_ref_known(v_code_2391_, 1);
v_a_3284_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3263_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3263_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; 
lean_dec_ref_known(v_code_2391_, 1);
v___x_3292_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3257_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec_ref(v___y_3096_);
return v___x_3292_;
}
}
case 6:
{
lean_object* v_type_3293_; uint8_t v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v_subst_3297_; lean_object* v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; uint8_t v___x_3301_; 
lean_dec_ref(v___y_3096_);
v_type_3293_ = lean_ctor_get(v_code_2391_, 0);
v___x_3294_ = 0;
v___x_3295_ = 0;
v___x_3296_ = lean_st_ref_get(v___y_3092_);
v_subst_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc_ref(v_subst_3297_);
lean_dec(v___x_3296_);
lean_inc_ref(v_type_3293_);
v___x_3298_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3294_, v_subst_3297_, v___x_3295_, v_type_3293_);
lean_dec_ref(v_subst_3297_);
v___x_3299_ = lean_ptr_addr(v_type_3293_);
v___x_3300_ = lean_ptr_addr(v___x_3298_);
v___x_3301_ = lean_usize_dec_eq(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3309_; 
v_isSharedCheck_3309_ = !lean_is_exclusive(v_code_2391_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v_code_2391_, 0);
lean_dec(v_unused_3310_);
v___x_3303_ = v_code_2391_;
v_isShared_3304_ = v_isSharedCheck_3309_;
goto v_resetjp_3302_;
}
else
{
lean_dec(v_code_2391_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3309_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3298_);
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3298_);
v___x_3306_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
}
else
{
lean_object* v___x_3311_; 
lean_dec_ref(v___x_3298_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_code_2391_);
return v___x_3311_;
}
}
default: 
{
lean_object* v_decl_3312_; lean_object* v_k_3313_; 
v_decl_3312_ = lean_ctor_get(v_code_2391_, 0);
v_k_3313_ = lean_ctor_get(v_code_2391_, 1);
lean_inc_ref(v_k_3313_);
lean_inc_ref(v_decl_3312_);
v_decl_2537_ = v_decl_3312_;
v_k_2538_ = v_k_3313_;
v___y_2539_ = v___y_3091_;
v___y_2540_ = v___y_3092_;
v___y_2541_ = v___y_3093_;
v___y_2542_ = v___y_3094_;
v___y_2543_ = v___y_3095_;
v___y_2544_ = v___y_3096_;
v___y_2545_ = v___y_3097_;
goto v___jp_2536_;
}
}
}
v___jp_3320_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_currRecDepth_3315_, v___x_3321_);
lean_dec(v_currRecDepth_3315_);
v___x_3323_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3323_, 0, v_toCold_3314_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
lean_ctor_set(v___x_3323_, 2, v_ref_3316_);
lean_ctor_set_uint16(v___x_3323_, sizeof(void*)*3, v_optionFlags_3317_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*3 + 2, v_suppressElabErrors_3318_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*3 + 3, v_isRecordingDeps_3319_);
v___x_3324_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2393_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v___x_3325_; lean_object* v_visited_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
lean_dec_ref_known(v___x_3324_, 1);
v___x_3325_ = lean_st_ref_get(v_a_2393_);
v_visited_3326_ = lean_ctor_get(v___x_3325_, 4);
lean_inc(v_visited_3326_);
lean_dec(v___x_3325_);
v___x_3327_ = lean_unsigned_to_nat(128u);
v___x_3328_ = lean_nat_mod(v_visited_3326_, v___x_3327_);
lean_dec(v_visited_3326_);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_nat_dec_eq(v___x_3328_, v___x_3329_);
lean_dec(v___x_3328_);
if (v___x_3330_ == 0)
{
v___y_3091_ = v_a_2392_;
v___y_3092_ = v_a_2393_;
v___y_3093_ = v_a_2394_;
v___y_3094_ = v_a_2395_;
v___y_3095_ = v_a_2396_;
v___y_3096_ = v___x_3323_;
v___y_3097_ = v_a_2398_;
goto v___jp_3090_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3332_ = l_Lean_Core_checkSystem(v___x_3331_, v___x_3323_, v_a_2398_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_dec_ref_known(v___x_3332_, 1);
v___y_3091_ = v_a_2392_;
v___y_3092_ = v_a_2393_;
v___y_3093_ = v_a_2394_;
v___y_3094_ = v_a_2395_;
v___y_3095_ = v_a_2396_;
v___y_3096_ = v___x_3323_;
v___y_3097_ = v_a_2398_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref_known(v___x_3323_, 3);
lean_dec_ref(v_code_2391_);
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref_known(v___x_3323_, 3);
lean_dec_ref(v_code_2391_);
v_a_3341_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3324_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3324_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simp_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2391_ = stack[0].m_obj;
lean_object* v_a_2392_ = stack[1].m_obj;
lean_object* v_a_2393_ = stack[2].m_obj;
lean_object* v_a_2394_ = stack[3].m_obj;
lean_object* v_a_2395_ = stack[4].m_obj;
lean_object* v_a_2396_ = stack[5].m_obj;
lean_object* v_a_2397_ = stack[6].m_obj;
lean_object* v_a_2398_ = stack[7].m_obj;
lean_object* v_res_3354_;
v_res_3354_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
stack->m_obj
 = v_res_3354_;
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_params_3364_; lean_object* v_type_3365_; lean_object* v_value_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v_subst_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_params_3364_ = lean_ctor_get(v_decl_3355_, 2);
v_type_3365_ = lean_ctor_get(v_decl_3355_, 3);
v_value_3366_ = lean_ctor_get(v_decl_3355_, 4);
v___x_3367_ = 0;
v___x_3368_ = 0;
v___x_3369_ = lean_st_ref_get(v_a_3357_);
v_subst_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc_ref(v_subst_3370_);
lean_dec(v___x_3369_);
lean_inc_ref(v_type_3365_);
v___x_3371_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3367_, v_subst_3370_, v___x_3368_, v_type_3365_);
lean_dec_ref(v_subst_3370_);
lean_inc_ref(v_params_3364_);
v___x_3372_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3367_, v___x_3368_, v_params_3364_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
lean_inc_ref(v_a_3361_);
lean_inc_ref(v_value_3366_);
v___x_3374_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3366_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3367_, v_decl_3355_, v___x_3371_, v_a_3373_, v_a_3375_, v_a_3360_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3373_);
lean_dec_ref(v___x_3371_);
lean_dec_ref(v_decl_3355_);
v_a_3377_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3374_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3374_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3371_);
lean_dec_ref(v_decl_3355_);
v_a_3385_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3372_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3372_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3355_ = stack[0].m_obj;
lean_object* v_a_3356_ = stack[1].m_obj;
lean_object* v_a_3357_ = stack[2].m_obj;
lean_object* v_a_3358_ = stack[3].m_obj;
lean_object* v_a_3359_ = stack[4].m_obj;
lean_object* v_a_3360_ = stack[5].m_obj;
lean_object* v_a_3361_ = stack[6].m_obj;
lean_object* v_a_3362_ = stack[7].m_obj;
lean_object* v_res_3393_;
v_res_3393_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
stack->m_obj
 = v_res_3393_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3404_, lean_object* v_i_3405_, lean_object* v_as_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3404_, v_i_3405_, v_as_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3426_, lean_object* v_k_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3426_, v_k_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
lean_dec(v_a_3444_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
return v_res_3446_;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3447_, uint8_t v_t_3448_, lean_object* v_decl_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3447_, v_t_3448_, v_decl_3449_, v___y_3451_, v___y_3454_);
return v___x_3458_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3447_ = stack[0].m_num;
uint8_t v_t_3448_ = stack[1].m_num;
lean_object* v_decl_3449_ = stack[2].m_obj;
lean_object* v___y_3450_ = stack[3].m_obj;
lean_object* v___y_3451_ = stack[4].m_obj;
lean_object* v___y_3452_ = stack[5].m_obj;
lean_object* v___y_3453_ = stack[6].m_obj;
lean_object* v___y_3454_ = stack[7].m_obj;
lean_object* v___y_3455_ = stack[8].m_obj;
lean_object* v___y_3456_ = stack[9].m_obj;
lean_object* v_res_3459_;
v_res_3459_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_3447_, v_t_3448_, v_decl_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
stack->m_obj
 = v_res_3459_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3460_, lean_object* v_t_3461_, lean_object* v_decl_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v_pu_boxed_3471_; uint8_t v_t_boxed_3472_; lean_object* v_res_3473_; 
v_pu_boxed_3471_ = lean_unbox(v_pu_3460_);
v_t_boxed_3472_ = lean_unbox(v_t_3461_);
v_res_3473_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3471_, v_t_boxed_3472_, v_decl_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
return v_res_3473_;
}
}
lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3474_, uint8_t v_t_3475_, lean_object* v_args_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3474_, v_t_3475_, v_args_3476_, v___y_3478_);
return v___x_3485_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3474_ = stack[0].m_num;
uint8_t v_t_3475_ = stack[1].m_num;
lean_object* v_args_3476_ = stack[2].m_obj;
lean_object* v___y_3477_ = stack[3].m_obj;
lean_object* v___y_3478_ = stack[4].m_obj;
lean_object* v___y_3479_ = stack[5].m_obj;
lean_object* v___y_3480_ = stack[6].m_obj;
lean_object* v___y_3481_ = stack[7].m_obj;
lean_object* v___y_3482_ = stack[8].m_obj;
lean_object* v___y_3483_ = stack[9].m_obj;
lean_object* v_res_3486_;
v_res_3486_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_3474_, v_t_3475_, v_args_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
stack->m_obj
 = v_res_3486_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3487_, lean_object* v_t_3488_, lean_object* v_args_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v_pu_boxed_3498_; uint8_t v_t_boxed_3499_; lean_object* v_res_3500_; 
v_pu_boxed_3498_ = lean_unbox(v_pu_3487_);
v_t_boxed_3499_ = lean_unbox(v_t_3488_);
v_res_3500_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3498_, v_t_boxed_3499_, v_args_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3501_, lean_object* v_R_3502_, lean_object* v_a_3503_, lean_object* v_b_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3503_, v_b_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_, lean_object* v_x_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3507_, v_x_3508_, v_x_3509_);
return v___x_3510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3511_, size_t v_i_3512_, size_t v_stop_3513_, lean_object* v_b_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3511_, v_i_3512_, v_stop_3513_, v_b_3514_, v___y_3516_);
return v___x_3523_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3511_ = stack[0].m_obj;
size_t v_i_3512_ = stack[1].m_num;
size_t v_stop_3513_ = stack[2].m_num;
lean_object* v_b_3514_ = stack[3].m_obj;
lean_object* v___y_3515_ = stack[4].m_obj;
lean_object* v___y_3516_ = stack[5].m_obj;
lean_object* v___y_3517_ = stack[6].m_obj;
lean_object* v___y_3518_ = stack[7].m_obj;
lean_object* v___y_3519_ = stack[8].m_obj;
lean_object* v___y_3520_ = stack[9].m_obj;
lean_object* v___y_3521_ = stack[10].m_obj;
lean_object* v_res_3524_;
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3511_, v_i_3512_, v_stop_3513_, v_b_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
stack->m_obj
 = v_res_3524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3525_, lean_object* v_i_3526_, lean_object* v_stop_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
size_t v_i_boxed_3537_; size_t v_stop_boxed_3538_; lean_object* v_res_3539_; 
v_i_boxed_3537_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_stop_boxed_3538_ = lean_unbox_usize(v_stop_3527_);
lean_dec(v_stop_3527_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3525_, v_i_boxed_3537_, v_stop_boxed_3538_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
return v_res_3539_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3540_, size_t v_i_3541_, size_t v_stop_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3540_, v_i_3541_, v_stop_3542_, v___y_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3540_ = stack[0].m_obj;
size_t v_i_3541_ = stack[1].m_num;
size_t v_stop_3542_ = stack[2].m_num;
lean_object* v___y_3543_ = stack[3].m_obj;
lean_object* v___y_3544_ = stack[4].m_obj;
lean_object* v___y_3545_ = stack[5].m_obj;
lean_object* v___y_3546_ = stack[6].m_obj;
lean_object* v___y_3547_ = stack[7].m_obj;
lean_object* v___y_3548_ = stack[8].m_obj;
lean_object* v___y_3549_ = stack[9].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3540_, v_i_3541_, v_stop_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3553_, lean_object* v_i_3554_, lean_object* v_stop_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
size_t v_i_boxed_3564_; size_t v_stop_boxed_3565_; lean_object* v_res_3566_; 
v_i_boxed_3564_ = lean_unbox_usize(v_i_3554_);
lean_dec(v_i_3554_);
v_stop_boxed_3565_ = lean_unbox_usize(v_stop_3555_);
lean_dec(v_stop_3555_);
v_res_3566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3553_, v_i_boxed_3564_, v_stop_boxed_3565_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v_as_3553_);
return v_res_3566_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3567_, size_t v_i_3568_, size_t v_stop_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3567_, v_i_3568_, v_stop_3569_, v_b_3570_, v___y_3572_);
return v___x_3576_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3567_ = stack[0].m_obj;
size_t v_i_3568_ = stack[1].m_num;
size_t v_stop_3569_ = stack[2].m_num;
lean_object* v_b_3570_ = stack[3].m_obj;
lean_object* v___y_3571_ = stack[4].m_obj;
lean_object* v___y_3572_ = stack[5].m_obj;
lean_object* v___y_3573_ = stack[6].m_obj;
lean_object* v___y_3574_ = stack[7].m_obj;
lean_object* v_res_3577_;
v_res_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3567_, v_i_3568_, v_stop_3569_, v_b_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
stack->m_obj
 = v_res_3577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3578_, lean_object* v_i_3579_, lean_object* v_stop_3580_, lean_object* v_b_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
size_t v_i_boxed_3587_; size_t v_stop_boxed_3588_; lean_object* v_res_3589_; 
v_i_boxed_3587_ = lean_unbox_usize(v_i_3579_);
lean_dec(v_i_3579_);
v_stop_boxed_3588_ = lean_unbox_usize(v_stop_3580_);
lean_dec(v_stop_3580_);
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3578_, v_i_boxed_3587_, v_stop_boxed_3588_, v_b_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v_as_3578_);
return v_res_3589_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3590_, size_t v_i_3591_, size_t v_stop_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3590_, v_i_3591_, v_stop_3592_, v_b_3593_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3602_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3590_ = stack[0].m_obj;
size_t v_i_3591_ = stack[1].m_num;
size_t v_stop_3592_ = stack[2].m_num;
lean_object* v_b_3593_ = stack[3].m_obj;
lean_object* v___y_3594_ = stack[4].m_obj;
lean_object* v___y_3595_ = stack[5].m_obj;
lean_object* v___y_3596_ = stack[6].m_obj;
lean_object* v___y_3597_ = stack[7].m_obj;
lean_object* v___y_3598_ = stack[8].m_obj;
lean_object* v___y_3599_ = stack[9].m_obj;
lean_object* v___y_3600_ = stack[10].m_obj;
lean_object* v_res_3603_;
v_res_3603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3590_, v_i_3591_, v_stop_3592_, v_b_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
stack->m_obj
 = v_res_3603_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3604_, lean_object* v_i_3605_, lean_object* v_stop_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
size_t v_i_boxed_3616_; size_t v_stop_boxed_3617_; lean_object* v_res_3618_; 
v_i_boxed_3616_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_stop_boxed_3617_ = lean_unbox_usize(v_stop_3606_);
lean_dec(v_stop_3606_);
v_res_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3604_, v_i_boxed_3616_, v_stop_boxed_3617_, v_b_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3619_, size_t v_i_3620_, size_t v_stop_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3619_, v_i_3620_, v_stop_3621_, v_b_3622_, v___y_3627_);
return v___x_3631_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3619_ = stack[0].m_obj;
size_t v_i_3620_ = stack[1].m_num;
size_t v_stop_3621_ = stack[2].m_num;
lean_object* v_b_3622_ = stack[3].m_obj;
lean_object* v___y_3623_ = stack[4].m_obj;
lean_object* v___y_3624_ = stack[5].m_obj;
lean_object* v___y_3625_ = stack[6].m_obj;
lean_object* v___y_3626_ = stack[7].m_obj;
lean_object* v___y_3627_ = stack[8].m_obj;
lean_object* v___y_3628_ = stack[9].m_obj;
lean_object* v___y_3629_ = stack[10].m_obj;
lean_object* v_res_3632_;
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3619_, v_i_3620_, v_stop_3621_, v_b_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
stack->m_obj
 = v_res_3632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3633_, lean_object* v_i_3634_, lean_object* v_stop_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
size_t v_i_boxed_3645_; size_t v_stop_boxed_3646_; lean_object* v_res_3647_; 
v_i_boxed_3645_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_stop_boxed_3646_ = lean_unbox_usize(v_stop_3635_);
lean_dec(v_stop_3635_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3633_, v_i_boxed_3645_, v_stop_boxed_3646_, v_b_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_as_3633_);
return v_res_3647_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3648_, size_t v_i_3649_, size_t v_stop_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3648_, v_i_3649_, v_stop_3650_, v___y_3652_);
return v___x_3659_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3648_ = stack[0].m_obj;
size_t v_i_3649_ = stack[1].m_num;
size_t v_stop_3650_ = stack[2].m_num;
lean_object* v___y_3651_ = stack[3].m_obj;
lean_object* v___y_3652_ = stack[4].m_obj;
lean_object* v___y_3653_ = stack[5].m_obj;
lean_object* v___y_3654_ = stack[6].m_obj;
lean_object* v___y_3655_ = stack[7].m_obj;
lean_object* v___y_3656_ = stack[8].m_obj;
lean_object* v___y_3657_ = stack[9].m_obj;
lean_object* v_res_3660_;
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3648_, v_i_3649_, v_stop_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
stack->m_obj
 = v_res_3660_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3661_, lean_object* v_i_3662_, lean_object* v_stop_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
size_t v_i_boxed_3672_; size_t v_stop_boxed_3673_; lean_object* v_res_3674_; 
v_i_boxed_3672_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_stop_boxed_3673_ = lean_unbox_usize(v_stop_3663_);
lean_dec(v_stop_3663_);
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3661_, v_i_boxed_3672_, v_stop_boxed_3673_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec_ref(v_as_3661_);
return v_res_3674_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3675_, size_t v_sz_3676_, size_t v_i_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3675_, v_sz_3676_, v_i_3677_, v_b_3678_, v___y_3680_);
return v___x_3687_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3675_ = stack[0].m_obj;
size_t v_sz_3676_ = stack[1].m_num;
size_t v_i_3677_ = stack[2].m_num;
lean_object* v_b_3678_ = stack[3].m_obj;
lean_object* v___y_3679_ = stack[4].m_obj;
lean_object* v___y_3680_ = stack[5].m_obj;
lean_object* v___y_3681_ = stack[6].m_obj;
lean_object* v___y_3682_ = stack[7].m_obj;
lean_object* v___y_3683_ = stack[8].m_obj;
lean_object* v___y_3684_ = stack[9].m_obj;
lean_object* v___y_3685_ = stack[10].m_obj;
lean_object* v_res_3688_;
v_res_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3675_, v_sz_3676_, v_i_3677_, v_b_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
stack->m_obj
 = v_res_3688_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3689_, lean_object* v_sz_3690_, lean_object* v_i_3691_, lean_object* v_b_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3690_);
lean_dec(v_sz_3690_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3691_);
lean_dec(v_i_3691_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3689_, v_sz_boxed_3701_, v_i_boxed_3702_, v_b_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v_as_3689_);
return v_res_3703_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3704_, lean_object* v_x_3705_, size_t v_x_3706_, size_t v_x_3707_, lean_object* v_x_3708_, lean_object* v_x_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3705_, v_x_3706_, v_x_3707_, v_x_3708_, v_x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3705_ = stack[1].m_obj;
size_t v_x_3706_ = stack[2].m_num;
size_t v_x_3707_ = stack[3].m_num;
lean_object* v_x_3708_ = stack[4].m_obj;
lean_object* v_x_3709_ = stack[5].m_obj;
lean_object* v_res_3711_;
v_res_3711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_box(0), v_x_3705_, v_x_3706_, v_x_3707_, v_x_3708_, v_x_3709_);
stack->m_obj
 = v_res_3711_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3712_, lean_object* v_x_3713_, lean_object* v_x_3714_, lean_object* v_x_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
size_t v_x_49997__boxed_3718_; size_t v_x_49998__boxed_3719_; lean_object* v_res_3720_; 
v_x_49997__boxed_3718_ = lean_unbox_usize(v_x_3714_);
lean_dec(v_x_3714_);
v_x_49998__boxed_3719_ = lean_unbox_usize(v_x_3715_);
lean_dec(v_x_3715_);
v_res_3720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3712_, v_x_3713_, v_x_49997__boxed_3718_, v_x_49998__boxed_3719_, v_x_3716_, v_x_3717_);
return v_res_3720_;
}
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3721_, uint8_t v_t_3722_, lean_object* v_i_3723_, lean_object* v_as_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3721_, v_t_3722_, v_i_3723_, v_as_3724_, v___y_3726_, v___y_3729_);
return v___x_3733_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3721_ = stack[0].m_num;
uint8_t v_t_3722_ = stack[1].m_num;
lean_object* v_i_3723_ = stack[2].m_obj;
lean_object* v_as_3724_ = stack[3].m_obj;
lean_object* v___y_3725_ = stack[4].m_obj;
lean_object* v___y_3726_ = stack[5].m_obj;
lean_object* v___y_3727_ = stack[6].m_obj;
lean_object* v___y_3728_ = stack[7].m_obj;
lean_object* v___y_3729_ = stack[8].m_obj;
lean_object* v___y_3730_ = stack[9].m_obj;
lean_object* v___y_3731_ = stack[10].m_obj;
lean_object* v_res_3734_;
v_res_3734_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_3721_, v_t_3722_, v_i_3723_, v_as_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
stack->m_obj
 = v_res_3734_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3735_, lean_object* v_t_3736_, lean_object* v_i_3737_, lean_object* v_as_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v_pu_boxed_3747_; uint8_t v_t_boxed_3748_; lean_object* v_res_3749_; 
v_pu_boxed_3747_ = lean_unbox(v_pu_3735_);
v_t_boxed_3748_ = lean_unbox(v_t_3736_);
v_res_3749_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3747_, v_t_boxed_3748_, v_i_3737_, v_as_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3750_, lean_object* v_n_3751_, lean_object* v_k_3752_, lean_object* v_v_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3751_, v_k_3752_, v_v_3753_);
return v___x_3754_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3755_, size_t v_depth_3756_, lean_object* v_keys_3757_, lean_object* v_vals_3758_, lean_object* v_heq_3759_, lean_object* v_i_3760_, lean_object* v_entries_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3756_, v_keys_3757_, v_vals_3758_, v_i_3760_, v_entries_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3756_ = stack[1].m_num;
lean_object* v_keys_3757_ = stack[2].m_obj;
lean_object* v_vals_3758_ = stack[3].m_obj;
lean_object* v_i_3760_ = stack[5].m_obj;
lean_object* v_entries_3761_ = stack[6].m_obj;
lean_object* v_res_3763_;
v_res_3763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_box(0), v_depth_3756_, v_keys_3757_, v_vals_3758_, lean_box(0), v_i_3760_, v_entries_3761_);
stack->m_obj
 = v_res_3763_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3764_, lean_object* v_depth_3765_, lean_object* v_keys_3766_, lean_object* v_vals_3767_, lean_object* v_heq_3768_, lean_object* v_i_3769_, lean_object* v_entries_3770_){
_start:
{
size_t v_depth_boxed_3771_; lean_object* v_res_3772_; 
v_depth_boxed_3771_ = lean_unbox_usize(v_depth_3765_);
lean_dec(v_depth_3765_);
v_res_3772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3764_, v_depth_boxed_3771_, v_keys_3766_, v_vals_3767_, v_heq_3768_, v_i_3769_, v_entries_3770_);
lean_dec_ref(v_vals_3767_);
lean_dec_ref(v_keys_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3774_, v_x_3775_, v_x_3776_, v_x_3777_);
return v___x_3778_;
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
