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
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_1_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* v_c_2_){
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* v_c_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_23_);
lean_dec_ref(v_c_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* v_c_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_c_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* v_c_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(v_c_28_);
lean_dec_ref(v_c_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* v_a_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
else
{
lean_object* v_key_34_; lean_object* v_tail_35_; uint8_t v___x_36_; 
v_key_34_ = lean_ctor_get(v_x_32_, 0);
v_tail_35_ = lean_ctor_get(v_x_32_, 2);
v___x_36_ = l_Lean_instBEqFVarId_beq(v_key_34_, v_a_31_);
if (v___x_36_ == 0)
{
v_x_32_ = v_tail_35_;
goto _start;
}
else
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* v_a_38_, lean_object* v_x_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_a_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
return v_x_42_;
}
else
{
lean_object* v_key_44_; lean_object* v_value_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_69_; 
v_key_44_ = lean_ctor_get(v_x_43_, 0);
v_value_45_ = lean_ctor_get(v_x_43_, 1);
v_tail_46_ = lean_ctor_get(v_x_43_, 2);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_69_ == 0)
{
v___x_48_ = v_x_43_;
v_isShared_49_ = v_isSharedCheck_69_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_value_45_);
lean_inc(v_key_44_);
lean_dec(v_x_43_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_69_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v_fold_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_50_ = lean_array_get_size(v_x_42_);
v___x_51_ = l_Lean_instHashableFVarId_hash(v_key_44_);
v___x_52_ = 32ULL;
v___x_53_ = lean_uint64_shift_right(v___x_51_, v___x_52_);
v_fold_54_ = lean_uint64_xor(v___x_51_, v___x_53_);
v___x_55_ = 16ULL;
v___x_56_ = lean_uint64_shift_right(v_fold_54_, v___x_55_);
v___x_57_ = lean_uint64_xor(v_fold_54_, v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = lean_usize_of_nat(v___x_50_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_sub(v___x_59_, v___x_60_);
v___x_62_ = lean_usize_land(v___x_58_, v___x_61_);
v___x_63_ = lean_array_uget_borrowed(v_x_42_, v___x_62_);
lean_inc(v___x_63_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 2, v___x_63_);
v___x_65_ = v___x_48_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_key_44_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_value_45_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___x_63_);
v___x_65_ = v_reuseFailAlloc_68_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_array_uset(v_x_42_, v___x_62_, v___x_65_);
v_x_42_ = v___x_66_;
v_x_43_ = v_tail_46_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object* v_i_70_, lean_object* v_source_71_, lean_object* v_target_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_array_get_size(v_source_71_);
v___x_74_ = lean_nat_dec_lt(v_i_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_dec_ref(v_source_71_);
lean_dec(v_i_70_);
return v_target_72_;
}
else
{
lean_object* v_es_75_; lean_object* v___x_76_; lean_object* v_source_77_; lean_object* v_target_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_es_75_ = lean_array_fget(v_source_71_, v_i_70_);
v___x_76_ = lean_box(0);
v_source_77_ = lean_array_fset(v_source_71_, v_i_70_, v___x_76_);
v_target_78_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_target_72_, v_es_75_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_i_70_, v___x_79_);
lean_dec(v_i_70_);
v_i_70_ = v___x_80_;
v_source_71_ = v_source_77_;
v_target_72_ = v_target_78_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* v_data_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_nbuckets_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_83_ = lean_array_get_size(v_data_82_);
v___x_84_ = lean_unsigned_to_nat(2u);
v_nbuckets_85_ = lean_nat_mul(v___x_83_, v___x_84_);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_box(0);
v___x_88_ = lean_mk_array(v_nbuckets_85_, v___x_87_);
v___x_89_ = lean_array_propagate_mark(v_data_82_, v___x_88_);
v___x_90_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_86_, v_data_82_, v___x_89_);
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
lean_object* v___x_228_; lean_object* v_fvarId_229_; lean_object* v_type_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_228_ = lean_array_fget_borrowed(v_array_215_, v_start_216_);
v_fvarId_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_fvarId_229_);
v_type_230_ = lean_ctor_get(v___x_228_, 2);
lean_inc_ref(v_type_230_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_start_216_, v___x_231_);
lean_dec(v_start_216_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_232_);
v___x_234_ = v___x_219_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_array_215_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_stop_217_);
v___x_234_ = v_reuseFailAlloc_265_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
uint8_t v___x_235_; lean_object* v___x_236_; 
v___x_235_ = 0;
v___x_236_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(v___x_235_, v_type_230_, v_fst_223_, v___x_221_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = 0;
v___x_239_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_235_, v_a_237_, v___x_238_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v_fvarId_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v_fvarId_241_ = lean_ctor_get(v_a_240_, 0);
lean_inc(v_fvarId_241_);
v___x_242_ = lean_array_push(v_snd_224_, v_a_240_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_fvarId_241_);
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
v_a_208_ = v___x_234_;
v_b_209_ = v___x_246_;
goto _start;
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___x_234_);
lean_dec(v_fvarId_229_);
lean_del_object(v___x_226_);
lean_dec(v_snd_224_);
lean_dec(v_fst_223_);
v_a_249_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_239_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_239_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v___x_234_);
lean_dec(v_fvarId_229_);
lean_del_object(v___x_226_);
lean_dec(v_snd_224_);
lean_dec(v_fst_223_);
v_a_257_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_236_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_236_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
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
lean_object* v_config_627_; uint8_t v_etaPoly_628_; 
v_config_627_ = lean_ctor_get(v_a_616_, 1);
v_etaPoly_628_ = lean_ctor_get_uint8(v_config_627_, 0);
if (v_etaPoly_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_letDecl_615_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v_value_631_; 
v_value_631_ = lean_ctor_get(v_letDecl_615_, 3);
lean_inc(v_value_631_);
if (lean_obj_tag(v_value_631_) == 3)
{
lean_object* v_fvarId_632_; lean_object* v_type_633_; lean_object* v_declName_634_; lean_object* v_us_635_; lean_object* v_args_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_796_; 
v_fvarId_632_ = lean_ctor_get(v_letDecl_615_, 0);
v_type_633_ = lean_ctor_get(v_letDecl_615_, 2);
v_declName_634_ = lean_ctor_get(v_value_631_, 0);
v_us_635_ = lean_ctor_get(v_value_631_, 1);
v_args_636_ = lean_ctor_get(v_value_631_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_value_631_);
if (v_isSharedCheck_796_ == 0)
{
v___x_638_ = v_value_631_;
v_isShared_639_ = v_isSharedCheck_796_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_args_636_);
lean_inc(v_us_635_);
lean_inc(v_declName_634_);
lean_dec(v_value_631_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_796_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v_env_641_; uint8_t v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_st_ref_get(v_a_622_);
v_env_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_env_641_);
lean_dec(v___x_640_);
v___x_642_ = 0;
lean_inc(v_declName_634_);
v___x_643_ = l_Lean_Environment_find_x3f(v_env_641_, v_declName_634_, v___x_642_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_ConstantInfo_type(v_val_644_);
lean_dec(v_val_644_);
v___x_646_ = l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_645_, v_a_622_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_785_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_785_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_785_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_785_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; 
v___x_651_ = lean_unbox(v_a_647_);
lean_dec(v_a_647_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_654_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v___x_652_ = lean_box(0);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_649_);
lean_inc(v_declName_634_);
v___x_656_ = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_634_, v_a_622_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_784_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_784_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_784_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_783_; 
v_val_661_ = lean_ctor_get(v_a_657_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_783_ == 0)
{
v___x_663_ = v_a_657_;
v_isShared_664_ = v_isSharedCheck_783_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_a_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_783_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
uint8_t v___x_665_; 
v___x_665_ = lean_unbox(v_val_661_);
lean_dec(v_val_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_del_object(v___x_659_);
v___x_666_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_619_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; uint8_t v___x_668_; lean_object* v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_unbox(v_a_667_);
lean_inc(v_declName_634_);
v___x_669_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_634_, v___x_668_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_762_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_762_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_762_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_762_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
if (lean_obj_tag(v_a_670_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_761_; 
v_val_674_ = lean_ctor_get(v_a_670_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_761_ == 0)
{
v___x_676_ = v_a_670_;
v_isShared_677_ = v_isSharedCheck_761_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v_a_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_761_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
uint8_t v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unbox(v_a_667_);
lean_dec(v_a_667_);
v___x_679_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_array_get_size(v_args_636_);
v___x_681_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_674_);
lean_dec(v_val_674_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_685_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v___x_683_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_683_);
v___x_685_ = v___x_672_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
else
{
lean_object* v___x_687_; 
lean_del_object(v___x_672_);
lean_inc_ref(v_type_633_);
v___x_687_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_679_, v_type_633_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_n(v_a_688_, 2);
lean_dec_ref_known(v___x_687_, 1);
v_sz_689_ = lean_array_size(v_a_688_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_689_, v___x_690_, v_a_688_);
v___x_692_ = l_Array_append___redArg(v_args_636_, v___x_691_);
lean_dec_ref(v___x_691_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 2, v___x_692_);
v___x_694_ = v___x_638_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_declName_634_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_us_635_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v___x_692_);
v___x_694_ = v_reuseFailAlloc_752_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_696_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_679_, v___x_694_, v___x_695_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_fvarId_698_; lean_object* v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v_fvarId_698_ = lean_ctor_get(v_a_697_, 0);
lean_inc(v_fvarId_698_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 5);
lean_ctor_set(v___x_663_, 0, v_fvarId_698_);
v___x_700_ = v___x_663_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fvarId_698_);
v___x_700_ = v_reuseFailAlloc_743_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_a_697_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_703_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_688_, v___x_701_, v___x_702_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_fvarId_705_; lean_object* v___x_707_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v_fvarId_705_ = lean_ctor_get(v_a_704_, 0);
lean_inc(v_fvarId_705_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_a_704_);
v___x_707_ = v___x_676_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_704_);
v___x_707_ = v_reuseFailAlloc_734_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
lean_inc(v_fvarId_632_);
v___x_708_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_632_, v_fvarId_705_, v_a_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_709_; 
lean_dec_ref_known(v___x_708_, 1);
v___x_709_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_615_, v_a_617_, v_a_620_);
lean_dec_ref(v_letDecl_615_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_709_, 0);
lean_dec(v_unused_717_);
v___x_711_ = v___x_709_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_709_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_707_);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_707_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___x_707_);
v_a_718_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v___x_707_);
lean_dec_ref(v_letDecl_615_);
v_a_726_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_708_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_708_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_del_object(v___x_676_);
lean_dec_ref(v_letDecl_615_);
v_a_735_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_703_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_703_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_688_);
lean_del_object(v___x_676_);
lean_del_object(v___x_663_);
lean_dec_ref(v_letDecl_615_);
v_a_744_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_696_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_696_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_del_object(v___x_676_);
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v_a_753_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_687_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_687_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_del_object(v___x_676_);
lean_dec(v_val_674_);
lean_del_object(v___x_672_);
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_624_;
}
}
}
else
{
lean_del_object(v___x_672_);
lean_dec(v_a_670_);
lean_dec(v_a_667_);
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
goto v___jp_624_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_667_);
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v_a_763_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_669_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_669_);
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
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v_a_771_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_666_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_666_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; 
lean_del_object(v___x_663_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v___x_779_ = lean_box(0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_779_);
v___x_781_ = v___x_659_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
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
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v_a_786_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_646_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_646_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___x_643_);
lean_del_object(v___x_638_);
lean_dec_ref(v_args_636_);
lean_dec(v_us_635_);
lean_dec(v_declName_634_);
lean_dec_ref(v_letDecl_615_);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_value_631_);
lean_dec_ref(v_letDecl_615_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
v___jp_624_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* v_letDecl_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v_letDecl_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t v___x_809_, size_t v_sz_810_, size_t v_i_811_, lean_object* v_bs_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_810_, v_i_811_, v_bs_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* v___x_814_, lean_object* v_sz_815_, lean_object* v_i_816_, lean_object* v_bs_817_){
_start:
{
uint8_t v___x_23070__boxed_818_; size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v___x_23070__boxed_818_ = lean_unbox(v___x_814_);
v_sz_boxed_819_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_820_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_23070__boxed_818_, v_sz_boxed_819_, v_i_boxed_820_, v_bs_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* v_c_822_, lean_object* v_fvarId_823_, lean_object* v_a_824_){
_start:
{
if (lean_obj_tag(v_c_822_) == 5)
{
lean_object* v_fvarId_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_848_; 
v_fvarId_826_ = lean_ctor_get(v_c_822_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_c_822_);
if (v_isSharedCheck_848_ == 0)
{
v___x_828_ = v_c_822_;
v_isShared_829_ = v_isSharedCheck_848_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_fvarId_826_);
lean_dec(v_c_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_848_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v_subst_832_; lean_object* v___x_833_; 
v___x_830_ = 0;
v___x_831_ = lean_st_ref_get(v_a_824_);
v_subst_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_subst_832_);
lean_dec(v___x_831_);
v___x_833_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_832_, v_fvarId_826_, v___x_830_);
lean_dec_ref(v_subst_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_fvarId_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_828_);
v_fvarId_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_fvarId_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_instBEqFVarId_beq(v_fvarId_834_, v_fvarId_823_);
lean_dec(v_fvarId_834_);
v___x_839_ = lean_box(v___x_838_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_box(v___x_830_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_844_);
v___x_846_ = v___x_828_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v_c_822_);
v___x_849_ = 0;
v___x_850_ = lean_box(v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* v_c_852_, lean_object* v_fvarId_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_852_, v_fvarId_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec(v_fvarId_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* v_c_857_, lean_object* v_fvarId_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_857_, v_fvarId_858_, v_a_860_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* v_c_868_, lean_object* v_fvarId_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(v_c_868_, v_fvarId_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_fvarId_869_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* v_value_879_){
_start:
{
if (lean_obj_tag(v_value_879_) == 4)
{
lean_object* v_fvarId_884_; lean_object* v_args_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_fvarId_884_ = lean_ctor_get(v_value_879_, 0);
v_args_885_ = lean_ctor_get(v_value_879_, 1);
v___x_886_ = lean_array_get_size(v_args_885_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_nat_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
goto v___jp_881_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_inc(v_fvarId_884_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_fvarId_884_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
else
{
goto v___jp_881_;
}
v___jp_881_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* v_value_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_891_);
lean_dec(v_value_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* v_value_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_894_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* v_value_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(v_value_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_value_904_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* v_a_914_, lean_object* v___x_915_, lean_object* v_fvarId_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_fvarId_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_fvarId_922_ = lean_ctor_get(v_a_914_, 0);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_fvarId_916_);
v___x_924_ = lean_mk_empty_array_with_capacity(v___x_915_);
v___x_925_ = lean_array_push(v___x_924_, v___x_923_);
lean_inc(v_fvarId_922_);
v___x_926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_926_, 0, v_fvarId_922_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* v_a_928_, lean_object* v___x_929_, lean_object* v_fvarId_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(v_a_928_, v___x_929_, v_fvarId_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___x_929_);
lean_dec_ref(v_a_928_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t v_pu_937_, uint8_t v_t_938_, lean_object* v_args_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_subst_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_subst_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_subst_943_);
lean_dec(v___x_942_);
v___x_944_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_937_, v_subst_943_, v_args_939_, v_t_938_);
lean_dec_ref(v_subst_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* v_pu_946_, lean_object* v_t_947_, lean_object* v_args_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v_pu_boxed_951_; uint8_t v_t_boxed_952_; lean_object* v_res_953_; 
v_pu_boxed_951_ = lean_unbox(v_pu_946_);
v_t_boxed_952_ = lean_unbox(v_t_947_);
v_res_953_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_boxed_951_, v_t_boxed_952_, v_args_948_, v___y_949_);
lean_dec(v___y_949_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* v_as_954_, size_t v_i_955_, size_t v_stop_956_, lean_object* v_b_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_eq(v_i_955_, v_stop_956_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_array_uget_borrowed(v_as_954_, v_i_955_);
lean_inc(v___x_961_);
v___x_962_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_961_, v___y_958_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; size_t v___x_964_; size_t v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_add(v_i_955_, v___x_964_);
v_i_955_ = v___x_965_;
v_b_957_ = v_a_963_;
goto _start;
}
else
{
return v___x_962_;
}
}
else
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_b_957_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
size_t v_i_boxed_974_; size_t v_stop_boxed_975_; lean_object* v_res_976_; 
v_i_boxed_974_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_975_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_968_, v_i_boxed_974_, v_stop_boxed_975_, v_b_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v_as_968_);
return v_res_976_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v_as_977_, size_t v_i_978_, size_t v_stop_979_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_eq(v_i_978_, v_stop_979_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; lean_object* v___y_983_; lean_object* v___x_987_; 
v___x_981_ = 1;
v___x_987_ = lean_array_uget_borrowed(v_as_977_, v_i_978_);
switch(lean_obj_tag(v___x_987_))
{
case 0:
{
lean_object* v_code_988_; 
v_code_988_ = lean_ctor_get(v___x_987_, 2);
v___y_983_ = v_code_988_;
goto v___jp_982_;
}
case 1:
{
lean_object* v_code_989_; 
v_code_989_ = lean_ctor_get(v___x_987_, 1);
v___y_983_ = v_code_989_;
goto v___jp_982_;
}
default: 
{
lean_object* v_code_990_; 
v_code_990_ = lean_ctor_get(v___x_987_, 0);
v___y_983_ = v_code_990_;
goto v___jp_982_;
}
}
v___jp_982_:
{
if (lean_obj_tag(v___y_983_) == 6)
{
size_t v___x_984_; size_t v___x_985_; 
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_978_, v___x_984_);
v_i_978_ = v___x_985_;
goto _start;
}
else
{
return v___x_981_;
}
}
}
else
{
uint8_t v___x_991_; 
v___x_991_ = 0;
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_stop_994_){
_start:
{
size_t v_i_boxed_995_; size_t v_stop_boxed_996_; uint8_t v_res_997_; lean_object* v_r_998_; 
v_i_boxed_995_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_stop_boxed_996_ = lean_unbox_usize(v_stop_994_);
lean_dec(v_stop_994_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_992_, v_i_boxed_995_, v_stop_boxed_996_);
lean_dec_ref(v_as_992_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_999_, uint8_t v_t_1000_, lean_object* v_i_1001_, lean_object* v_as_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_array_get_size(v_as_1002_);
v___x_1007_ = lean_nat_dec_lt(v_i_1001_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_i_1001_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_as_1002_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; lean_object* v_type_1010_; lean_object* v___x_1011_; lean_object* v_subst_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1009_ = lean_array_fget_borrowed(v_as_1002_, v_i_1001_);
v_type_1010_ = lean_ctor_get(v_a_1009_, 2);
v___x_1011_ = lean_st_ref_get(v___y_1003_);
v_subst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_subst_1012_);
lean_dec(v___x_1011_);
lean_inc_ref(v_type_1010_);
v___x_1013_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_999_, v_subst_1012_, v_t_1000_, v_type_1010_);
lean_dec_ref(v_subst_1012_);
lean_inc(v_a_1009_);
v___x_1014_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_999_, v_a_1009_, v___x_1013_, v___y_1004_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; size_t v___x_1016_; size_t v___x_1017_; uint8_t v___x_1018_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_ptr_addr(v_a_1009_);
v___x_1017_ = lean_ptr_addr(v_a_1015_);
v___x_1018_ = lean_usize_dec_eq(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_1001_, v___x_1019_);
v___x_1021_ = lean_array_fset(v_as_1002_, v_i_1001_, v_a_1015_);
lean_dec(v_i_1001_);
v_i_1001_ = v___x_1020_;
v_as_1002_ = v___x_1021_;
goto _start;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v_a_1015_);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_i_1001_, v___x_1023_);
lean_dec(v_i_1001_);
v_i_1001_ = v___x_1024_;
goto _start;
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_as_1002_);
lean_dec(v_i_1001_);
v_a_1026_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1014_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1014_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1034_, lean_object* v_t_1035_, lean_object* v_i_1036_, lean_object* v_as_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v_pu_boxed_1041_; uint8_t v_t_boxed_1042_; lean_object* v_res_1043_; 
v_pu_boxed_1041_ = lean_unbox(v_pu_1034_);
v_t_boxed_1042_ = lean_unbox(v_t_1035_);
v_res_1043_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1041_, v_t_boxed_1042_, v_i_1036_, v_as_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1044_, uint8_t v_t_1045_, lean_object* v_ps_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1044_, v_t_1045_, v___x_1055_, v_ps_1046_, v___y_1048_, v___y_1051_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1057_, lean_object* v_t_1058_, lean_object* v_ps_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_pu_boxed_1068_; uint8_t v_t_boxed_1069_; lean_object* v_res_1070_; 
v_pu_boxed_1068_ = lean_unbox(v_pu_1057_);
v_t_boxed_1069_ = lean_unbox(v_t_1058_);
v_res_1070_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1068_, v_t_boxed_1069_, v_ps_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1071_, uint8_t v_t_1072_, lean_object* v_decl_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_type_1077_; lean_object* v_value_1078_; lean_object* v___x_1079_; lean_object* v_subst_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_subst_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_type_1077_ = lean_ctor_get(v_decl_1073_, 2);
v_value_1078_ = lean_ctor_get(v_decl_1073_, 3);
v___x_1079_ = lean_st_ref_get(v___y_1074_);
v_subst_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_subst_1080_);
lean_dec(v___x_1079_);
lean_inc_ref(v_type_1077_);
v___x_1081_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1071_, v_subst_1080_, v_t_1072_, v_type_1077_);
lean_dec_ref(v_subst_1080_);
v___x_1082_ = lean_st_ref_get(v___y_1074_);
v_subst_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_subst_1083_);
lean_dec(v___x_1082_);
lean_inc(v_value_1078_);
v___x_1084_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1071_, v_subst_1083_, v_value_1078_, v_t_1072_);
lean_dec_ref(v_subst_1083_);
v___x_1085_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1071_, v_decl_1073_, v___x_1081_, v___x_1084_, v___y_1075_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1086_, lean_object* v_t_1087_, lean_object* v_decl_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v_pu_boxed_1092_; uint8_t v_t_boxed_1093_; lean_object* v_res_1094_; 
v_pu_boxed_1092_ = lean_unbox(v_pu_1086_);
v_t_boxed_1093_ = lean_unbox(v_t_1087_);
v_res_1094_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1092_, v_t_boxed_1093_, v_decl_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1095_, lean_object* v___f_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v_fvarId_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
lean_inc(v_fvarId_1099_);
v___x_1105_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1099_, v___y_1095_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; 
lean_dec_ref_known(v___x_1105_, 1);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1097_);
v___x_1106_ = lean_apply_9(v___f_1096_, v_fvarId_1099_, v___y_1097_, v___y_1095_, v___y_1098_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
return v___x_1106_;
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_fvarId_1099_);
lean_dec_ref(v___f_1096_);
v_a_1107_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1115_, lean_object* v___f_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v_fvarId_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1115_, v___f_1116_, v___y_1117_, v___y_1118_, v_fvarId_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1115_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_ks_1130_; lean_object* v_vs_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_ks_1130_ = lean_ctor_get(v_x_1126_, 0);
v_vs_1131_ = lean_ctor_get(v_x_1126_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_x_1126_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_vs_1131_);
lean_inc(v_ks_1130_);
lean_dec(v_x_1126_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_array_get_size(v_ks_1130_);
v___x_1136_ = lean_nat_dec_lt(v_x_1127_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_dec(v_x_1127_);
v___x_1137_ = lean_array_push(v_ks_1130_, v_x_1128_);
v___x_1138_ = lean_array_push(v_vs_1131_, v_x_1129_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1138_);
lean_ctor_set(v___x_1133_, 0, v___x_1137_);
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
lean_object* v_k_x27_1142_; uint8_t v___x_1143_; 
v_k_x27_1142_ = lean_array_fget_borrowed(v_ks_1130_, v_x_1127_);
v___x_1143_ = lean_name_eq(v_x_1128_, v_k_x27_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1145_; 
if (v_isShared_1134_ == 0)
{
v___x_1145_ = v___x_1133_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_ks_1130_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_vs_1131_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_nat_add(v_x_1127_, v___x_1146_);
lean_dec(v_x_1127_);
v_x_1126_ = v___x_1145_;
v_x_1127_ = v___x_1147_;
goto _start;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1150_ = lean_array_fset(v_ks_1130_, v_x_1127_, v_x_1128_);
v___x_1151_ = lean_array_fset(v_vs_1131_, v_x_1127_, v_x_1129_);
lean_dec(v_x_1127_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1151_);
lean_ctor_set(v___x_1133_, 0, v___x_1150_);
v___x_1153_ = v___x_1133_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1156_, lean_object* v_k_1157_, lean_object* v_v_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1156_, v___x_1159_, v_k_1157_, v_v_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1162_, size_t v_x_1163_, size_t v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_object* v_es_1167_; size_t v___x_1168_; size_t v___x_1169_; lean_object* v_j_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_es_1167_ = lean_ctor_get(v_x_1162_, 0);
v___x_1168_ = ((size_t)31ULL);
v___x_1169_ = lean_usize_land(v_x_1163_, v___x_1168_);
v_j_1170_ = lean_usize_to_nat(v___x_1169_);
v___x_1171_ = lean_array_get_size(v_es_1167_);
v___x_1172_ = lean_nat_dec_lt(v_j_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec(v_j_1170_);
lean_dec(v_x_1166_);
lean_dec(v_x_1165_);
return v_x_1162_;
}
else
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1211_; 
lean_inc_ref(v_es_1167_);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_x_1162_, 0);
lean_dec(v_unused_1212_);
v___x_1174_ = v_x_1162_;
v_isShared_1175_ = v_isSharedCheck_1211_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v_x_1162_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1211_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_v_1176_; lean_object* v___x_1177_; lean_object* v_xs_x27_1178_; lean_object* v___y_1180_; 
v_v_1176_ = lean_array_fget(v_es_1167_, v_j_1170_);
v___x_1177_ = lean_box(0);
v_xs_x27_1178_ = lean_array_fset(v_es_1167_, v_j_1170_, v___x_1177_);
switch(lean_obj_tag(v_v_1176_))
{
case 0:
{
lean_object* v_key_1185_; lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1196_; 
v_key_1185_ = lean_ctor_get(v_v_1176_, 0);
v_val_1186_ = lean_ctor_get(v_v_1176_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_v_1176_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1188_ = v_v_1176_;
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_inc(v_key_1185_);
lean_dec(v_v_1176_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_name_eq(v_x_1165_, v_key_1185_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_del_object(v___x_1188_);
v___x_1191_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1185_, v_val_1186_, v_x_1165_, v_x_1166_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
v___y_1180_ = v___x_1192_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1194_; 
lean_dec(v_val_1186_);
lean_dec(v_key_1185_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_x_1166_);
lean_ctor_set(v___x_1188_, 0, v_x_1165_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_x_1165_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_x_1166_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
v___y_1180_ = v___x_1194_;
goto v___jp_1179_;
}
}
}
}
case 1:
{
lean_object* v_node_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1209_; 
v_node_1197_ = lean_ctor_get(v_v_1176_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_v_1176_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1199_ = v_v_1176_;
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_node_1197_);
lean_dec(v_v_1176_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1201_ = ((size_t)5ULL);
v___x_1202_ = lean_usize_shift_right(v_x_1163_, v___x_1201_);
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_add(v_x_1164_, v___x_1203_);
v___x_1205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1197_, v___x_1202_, v___x_1204_, v_x_1165_, v_x_1166_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1205_);
v___x_1207_ = v___x_1199_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
v___y_1180_ = v___x_1207_;
goto v___jp_1179_;
}
}
}
default: 
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_x_1165_);
lean_ctor_set(v___x_1210_, 1, v_x_1166_);
v___y_1180_ = v___x_1210_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_array_fset(v_xs_x27_1178_, v_j_1170_, v___y_1180_);
lean_dec(v_j_1170_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1181_);
v___x_1183_ = v___x_1174_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
else
{
lean_object* v_ks_1213_; lean_object* v_vs_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1232_; 
v_ks_1213_ = lean_ctor_get(v_x_1162_, 0);
v_vs_1214_ = lean_ctor_get(v_x_1162_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1216_ = v_x_1162_;
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_vs_1214_);
lean_inc(v_ks_1213_);
lean_dec(v_x_1162_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_ks_1213_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_vs_1214_);
v___x_1219_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v_newNode_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v_newNode_1220_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1219_, v_x_1165_, v_x_1166_);
v___x_1221_ = ((size_t)7ULL);
v___x_1222_ = lean_usize_dec_le(v___x_1221_, v_x_1164_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1220_);
v___x_1224_ = lean_unsigned_to_nat(4u);
v___x_1225_ = lean_nat_dec_lt(v___x_1223_, v___x_1224_);
lean_dec(v___x_1223_);
if (v___x_1225_ == 0)
{
lean_object* v_ks_1226_; lean_object* v_vs_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_ks_1226_ = lean_ctor_get(v_newNode_1220_, 0);
lean_inc_ref(v_ks_1226_);
v_vs_1227_ = lean_ctor_get(v_newNode_1220_, 1);
lean_inc_ref(v_vs_1227_);
lean_dec_ref(v_newNode_1220_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1230_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1164_, v_ks_1226_, v_vs_1227_, v___x_1228_, v___x_1229_);
lean_dec_ref(v_vs_1227_);
lean_dec_ref(v_ks_1226_);
return v___x_1230_;
}
else
{
return v_newNode_1220_;
}
}
else
{
return v_newNode_1220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1233_, lean_object* v_keys_1234_, lean_object* v_vals_1235_, lean_object* v_i_1236_, lean_object* v_entries_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_array_get_size(v_keys_1234_);
v___x_1239_ = lean_nat_dec_lt(v_i_1236_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_i_1236_);
return v_entries_1237_;
}
else
{
lean_object* v_k_1240_; lean_object* v_v_1241_; uint64_t v___y_1243_; 
v_k_1240_ = lean_array_fget_borrowed(v_keys_1234_, v_i_1236_);
v_v_1241_ = lean_array_fget_borrowed(v_vals_1235_, v_i_1236_);
if (lean_obj_tag(v_k_1240_) == 0)
{
uint64_t v___x_1254_; 
v___x_1254_ = 1723ULL;
v___y_1243_ = v___x_1254_;
goto v___jp_1242_;
}
else
{
uint64_t v_hash_1255_; 
v_hash_1255_ = lean_ctor_get_uint64(v_k_1240_, sizeof(void*)*2);
v___y_1243_ = v_hash_1255_;
goto v___jp_1242_;
}
v___jp_1242_:
{
size_t v_h_1244_; size_t v___x_1245_; lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v_h_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_h_1244_ = lean_uint64_to_usize(v___y_1243_);
v___x_1245_ = ((size_t)5ULL);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_sub(v_depth_1233_, v___x_1247_);
v___x_1249_ = lean_usize_mul(v___x_1245_, v___x_1248_);
v_h_1250_ = lean_usize_shift_right(v_h_1244_, v___x_1249_);
v___x_1251_ = lean_nat_add(v_i_1236_, v___x_1246_);
lean_dec(v_i_1236_);
lean_inc(v_v_1241_);
lean_inc(v_k_1240_);
v___x_1252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1237_, v_h_1250_, v_depth_1233_, v_k_1240_, v_v_1241_);
v_i_1236_ = v___x_1251_;
v_entries_1237_ = v___x_1252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1256_, lean_object* v_keys_1257_, lean_object* v_vals_1258_, lean_object* v_i_1259_, lean_object* v_entries_1260_){
_start:
{
size_t v_depth_boxed_1261_; lean_object* v_res_1262_; 
v_depth_boxed_1261_ = lean_unbox_usize(v_depth_1256_);
lean_dec(v_depth_1256_);
v_res_1262_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1261_, v_keys_1257_, v_vals_1258_, v_i_1259_, v_entries_1260_);
lean_dec_ref(v_vals_1258_);
lean_dec_ref(v_keys_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
size_t v_x_43430__boxed_1268_; size_t v_x_43431__boxed_1269_; lean_object* v_res_1270_; 
v_x_43430__boxed_1268_ = lean_unbox_usize(v_x_1264_);
lean_dec(v_x_1264_);
v_x_43431__boxed_1269_ = lean_unbox_usize(v_x_1265_);
lean_dec(v_x_1265_);
v_res_1270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1263_, v_x_43430__boxed_1268_, v_x_43431__boxed_1269_, v_x_1266_, v_x_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
uint64_t v___y_1275_; 
if (lean_obj_tag(v_x_1272_) == 0)
{
uint64_t v___x_1279_; 
v___x_1279_ = 1723ULL;
v___y_1275_ = v___x_1279_;
goto v___jp_1274_;
}
else
{
uint64_t v_hash_1280_; 
v_hash_1280_ = lean_ctor_get_uint64(v_x_1272_, sizeof(void*)*2);
v___y_1275_ = v_hash_1280_;
goto v___jp_1274_;
}
v___jp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_uint64_to_usize(v___y_1275_);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1271_, v___x_1276_, v___x_1277_, v_x_1272_, v_x_1273_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v_array_1283_; lean_object* v_start_1284_; lean_object* v_stop_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1298_; 
v_array_1283_ = lean_ctor_get(v_a_1281_, 0);
v_start_1284_ = lean_ctor_get(v_a_1281_, 1);
v_stop_1285_ = lean_ctor_get(v_a_1281_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1287_ = v_a_1281_;
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_stop_1285_);
lean_inc(v_start_1284_);
lean_inc(v_array_1283_);
lean_dec(v_a_1281_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_nat_dec_lt(v_start_1284_, v_stop_1285_);
if (v___x_1289_ == 0)
{
lean_del_object(v___x_1287_);
lean_dec(v_stop_1285_);
lean_dec(v_start_1284_);
lean_dec_ref(v_array_1283_);
return v_b_1282_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v_start_1284_, v___x_1290_);
lean_inc_ref(v_array_1283_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1291_);
v___x_1293_ = v___x_1287_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_array_1283_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_stop_1285_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_array_fget(v_array_1283_, v_start_1284_);
lean_dec(v_start_1284_);
lean_dec_ref(v_array_1283_);
v___x_1295_ = lean_array_push(v_b_1282_, v___x_1294_);
v_a_1281_ = v___x_1293_;
v_b_1282_ = v___x_1295_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1299_, size_t v_sz_1300_, size_t v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_lt(v_i_1301_, v_sz_1300_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_b_1302_);
return v___x_1306_;
}
else
{
lean_object* v_array_1307_; lean_object* v_start_1308_; lean_object* v_stop_1309_; uint8_t v___x_1310_; 
v_array_1307_ = lean_ctor_get(v_b_1302_, 0);
v_start_1308_ = lean_ctor_get(v_b_1302_, 1);
v_stop_1309_ = lean_ctor_get(v_b_1302_, 2);
v___x_1310_ = lean_nat_dec_lt(v_start_1308_, v_stop_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_b_1302_);
return v___x_1311_;
}
else
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1344_; 
lean_inc(v_stop_1309_);
lean_inc(v_start_1308_);
lean_inc_ref(v_array_1307_);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_b_1302_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; lean_object* v_unused_1347_; 
v_unused_1345_ = lean_ctor_get(v_b_1302_, 2);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_b_1302_, 1);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_b_1302_, 0);
lean_dec(v_unused_1347_);
v___x_1313_ = v_b_1302_;
v_isShared_1314_ = v_isSharedCheck_1344_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v_b_1302_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1344_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_a_1315_; lean_object* v_fvarId_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v_a_1315_ = lean_array_uget_borrowed(v_as_1299_, v_i_1301_);
v_fvarId_1316_ = lean_ctor_get(v_a_1315_, 0);
v___x_1317_ = lean_array_fget(v_array_1307_, v_start_1308_);
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v_start_1308_, v___x_1318_);
lean_dec(v_start_1308_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1319_);
v___x_1321_ = v___x_1313_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_array_1307_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_stop_1309_);
v___x_1321_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v_subst_1323_; lean_object* v_used_1324_; lean_object* v_binderRenaming_1325_; lean_object* v_funDeclInfoMap_1326_; uint8_t v_simplified_1327_; lean_object* v_visited_1328_; lean_object* v_inline_1329_; lean_object* v_inlineLocal_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1342_; 
v___x_1322_ = lean_st_ref_take(v___y_1303_);
v_subst_1323_ = lean_ctor_get(v___x_1322_, 0);
v_used_1324_ = lean_ctor_get(v___x_1322_, 1);
v_binderRenaming_1325_ = lean_ctor_get(v___x_1322_, 2);
v_funDeclInfoMap_1326_ = lean_ctor_get(v___x_1322_, 3);
v_simplified_1327_ = lean_ctor_get_uint8(v___x_1322_, sizeof(void*)*7);
v_visited_1328_ = lean_ctor_get(v___x_1322_, 4);
v_inline_1329_ = lean_ctor_get(v___x_1322_, 5);
v_inlineLocal_1330_ = lean_ctor_get(v___x_1322_, 6);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1332_ = v___x_1322_;
v_isShared_1333_ = v_isSharedCheck_1342_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_inlineLocal_1330_);
lean_inc(v_inline_1329_);
lean_inc(v_visited_1328_);
lean_inc(v_funDeclInfoMap_1326_);
lean_inc(v_binderRenaming_1325_);
lean_inc(v_used_1324_);
lean_inc(v_subst_1323_);
lean_dec(v___x_1322_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1342_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_inc(v_fvarId_1316_);
v___x_1334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1323_, v_fvarId_1316_, v___x_1317_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_used_1324_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_binderRenaming_1325_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_funDeclInfoMap_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_visited_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 5, v_inline_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 6, v_inlineLocal_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*7, v_simplified_1327_);
v___x_1336_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; 
v___x_1337_ = lean_st_ref_put(v___y_1303_, v___x_1336_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1301_, v___x_1338_);
v_i_1301_ = v___x_1339_;
v_b_1302_ = v___x_1321_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1348_, lean_object* v_sz_1349_, lean_object* v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
size_t v_sz_boxed_1354_; size_t v_i_boxed_1355_; lean_object* v_res_1356_; 
v_sz_boxed_1354_ = lean_unbox_usize(v_sz_1349_);
lean_dec(v_sz_1349_);
v_i_boxed_1355_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1348_, v_sz_boxed_1354_, v_i_boxed_1355_, v_b_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v_as_1348_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1357_, size_t v_i_1358_, size_t v_stop_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_eq(v_i_1358_, v_stop_1359_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = 0;
v___x_1365_ = lean_array_uget_borrowed(v_as_1357_, v_i_1358_);
v___x_1366_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1364_, v___x_1365_, v___y_1361_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; size_t v___x_1368_; size_t v___x_1369_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_add(v_i_1358_, v___x_1368_);
v_i_1358_ = v___x_1369_;
v_b_1360_ = v_a_1367_;
goto _start;
}
else
{
return v___x_1366_;
}
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_b_1360_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1372_, lean_object* v_i_1373_, lean_object* v_stop_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
size_t v_i_boxed_1378_; size_t v_stop_boxed_1379_; lean_object* v_res_1380_; 
v_i_boxed_1378_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_stop_boxed_1379_ = lean_unbox_usize(v_stop_1374_);
lean_dec(v_stop_1374_);
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1372_, v_i_boxed_1378_, v_stop_boxed_1379_, v_b_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v_as_1372_);
return v_res_1380_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1384_ = lean_panic_fn_borrowed(v___x_1383_, v_msg_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1385_, size_t v_i_1386_, size_t v_stop_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_eq(v_i_1386_, v_stop_1387_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v_type_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1391_ = lean_array_uget_borrowed(v_as_1385_, v_i_1386_);
v_type_1392_ = lean_ctor_get(v___x_1391_, 2);
v___x_1393_ = 1;
v___x_1394_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1392_, v___y_1388_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1407_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1407_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1399_ == 0)
{
size_t v___x_1400_; size_t v___x_1401_; 
lean_del_object(v___x_1397_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_i_1386_, v___x_1400_);
v_i_1386_ = v___x_1401_;
goto _start;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(v___x_1393_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1403_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
return v___x_1394_;
}
}
else
{
uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = 0;
v___x_1409_ = lean_box(v___x_1408_);
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1411_, lean_object* v_i_1412_, lean_object* v_stop_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
size_t v_i_boxed_1416_; size_t v_stop_boxed_1417_; lean_object* v_res_1418_; 
v_i_boxed_1416_ = lean_unbox_usize(v_i_1412_);
lean_dec(v_i_1412_);
v_stop_boxed_1417_ = lean_unbox_usize(v_stop_1413_);
lean_dec(v_stop_1413_);
v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1411_, v_i_boxed_1416_, v_stop_boxed_1417_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v_as_1411_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1425_ == 0)
{
uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = 0;
v___x_1427_ = lean_array_uget_borrowed(v_as_1419_, v_i_1420_);
v___x_1428_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1426_, v___x_1427_, v___y_1423_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; size_t v___x_1430_; size_t v___x_1431_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1420_, v___x_1430_);
v_i_1420_ = v___x_1431_;
v_b_1422_ = v_a_1429_;
goto _start;
}
else
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1422_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1434_, lean_object* v_i_1435_, lean_object* v_stop_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
size_t v_i_boxed_1440_; size_t v_stop_boxed_1441_; lean_object* v_res_1442_; 
v_i_boxed_1440_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_stop_boxed_1441_ = lean_unbox_usize(v_stop_1436_);
lean_dec(v_stop_1436_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1434_, v_i_boxed_1440_, v_stop_boxed_1441_, v_b_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v_as_1434_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1443_, size_t v_i_1444_, size_t v_stop_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_a_1453_; lean_object* v___y_1458_; uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_eq(v_i_1444_, v_stop_1445_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_uget_borrowed(v_as_1443_, v_i_1444_);
v___x_1463_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1462_);
v___x_1464_ = lean_array_get_size(v___x_1463_);
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_nat_dec_lt(v___x_1461_, v___x_1464_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1463_);
v_a_1453_ = v___x_1465_;
goto v___jp_1452_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_le(v___x_1464_, v___x_1464_);
if (v___x_1467_ == 0)
{
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1463_);
v_a_1453_ = v___x_1465_;
goto v___jp_1452_;
}
else
{
size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1464_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1463_, v___x_1468_, v___x_1469_, v___x_1465_, v___y_1448_);
lean_dec_ref(v___x_1463_);
v___y_1458_ = v___x_1470_;
goto v___jp_1457_;
}
}
else
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1464_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1463_, v___x_1471_, v___x_1472_, v___x_1465_, v___y_1448_);
lean_dec_ref(v___x_1463_);
v___y_1458_ = v___x_1473_;
goto v___jp_1457_;
}
}
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_b_1446_);
return v___x_1474_;
}
v___jp_1452_:
{
size_t v___x_1454_; size_t v___x_1455_; 
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1444_, v___x_1454_);
v_i_1444_ = v___x_1455_;
v_b_1446_ = v_a_1453_;
goto _start;
}
v___jp_1457_:
{
if (lean_obj_tag(v___y_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___y_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___y_1458_, 1);
v_a_1453_ = v_a_1459_;
goto v___jp_1452_;
}
else
{
return v___y_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1475_, lean_object* v_i_1476_, lean_object* v_stop_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_i_boxed_1484_; size_t v_stop_boxed_1485_; lean_object* v_res_1486_; 
v_i_boxed_1484_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_stop_boxed_1485_ = lean_unbox_usize(v_stop_1477_);
lean_dec(v_stop_1477_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1475_, v_i_boxed_1484_, v_stop_boxed_1485_, v_b_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec_ref(v_as_1475_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1487_, size_t v_i_1488_, size_t v_stop_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_eq(v_i_1488_, v_stop_1489_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v_fvarId_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_array_uget_borrowed(v_as_1487_, v_i_1488_);
v_fvarId_1494_ = lean_ctor_get(v___x_1493_, 0);
v___x_1495_ = 1;
v___x_1496_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1494_, v___y_1490_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1509_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
if (v___x_1501_ == 0)
{
size_t v___x_1502_; size_t v___x_1503_; 
lean_del_object(v___x_1499_);
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = lean_usize_add(v_i_1488_, v___x_1502_);
v_i_1488_ = v___x_1503_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(v___x_1495_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1505_);
v___x_1507_ = v___x_1499_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
return v___x_1496_;
}
}
else
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = 0;
v___x_1511_ = lean_box(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1513_, lean_object* v_i_1514_, lean_object* v_stop_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_i_boxed_1518_; size_t v_stop_boxed_1519_; lean_object* v_res_1520_; 
v_i_boxed_1518_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_stop_boxed_1519_ = lean_unbox_usize(v_stop_1515_);
lean_dec(v_stop_1515_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1513_, v_i_boxed_1518_, v_stop_boxed_1519_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v_as_1513_);
return v_res_1520_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1524_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1525_ = lean_unsigned_to_nat(9u);
v___x_1526_ = lean_unsigned_to_nat(650u);
v___x_1527_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1528_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1529_ = l_mkPanicMessageWithDecl(v___x_1528_, v___x_1527_, v___x_1526_, v___x_1525_, v___x_1524_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(uint8_t v___x_1533_, lean_object* v_fvarId_1534_, lean_object* v_k_1535_, lean_object* v_args_1536_, uint8_t v___x_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v_result_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_lower_1551_; lean_object* v_upper_1552_; 
if (v___x_1533_ == 0)
{
lean_object* v___x_1579_; 
lean_dec(v___x_1540_);
lean_dec(v___x_1539_);
lean_dec(v___x_1538_);
lean_dec_ref(v_args_1536_);
v___x_1579_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1534_, v_result_1541_, v___y_1543_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref_known(v___x_1579_, 1);
lean_inc_ref(v___y_1547_);
v___x_1580_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1535_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1580_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_k_1535_);
v_a_1581_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1579_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_nat_dec_le(v___x_1538_, v___x_1539_);
if (v___x_1589_ == 0)
{
lean_dec(v___x_1539_);
v_lower_1551_ = v___x_1538_;
v_upper_1552_ = v___x_1540_;
goto v___jp_1550_;
}
else
{
lean_dec(v___x_1538_);
v_lower_1551_ = v___x_1539_;
v_upper_1552_ = v___x_1540_;
goto v___jp_1550_;
}
}
v___jp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1553_ = l_Array_toSubarray___redArg(v_args_1536_, v_lower_1551_, v_upper_1552_);
v___x_1554_ = l_Subarray_copy___redArg(v___x_1553_);
v___x_1555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_result_1541_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1557_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1537_, v___x_1555_, v___x_1556_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v_fvarId_1559_; lean_object* v___x_1560_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v_fvarId_1559_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_fvarId_1559_);
v___x_1560_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1534_, v_fvarId_1559_, v___y_1543_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref_known(v___x_1560_, 1);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1558_);
lean_ctor_set(v___x_1561_, 1, v_k_1535_);
lean_inc_ref(v___y_1547_);
v___x_1562_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1561_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1558_);
lean_dec_ref(v_k_1535_);
v_a_1563_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1560_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1560_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_k_1535_);
lean_dec(v_fvarId_1534_);
v_a_1571_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1557_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1557_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object** _args){
lean_object* v___x_1590_ = _args[0];
lean_object* v_fvarId_1591_ = _args[1];
lean_object* v_k_1592_ = _args[2];
lean_object* v_args_1593_ = _args[3];
lean_object* v___x_1594_ = _args[4];
lean_object* v___x_1595_ = _args[5];
lean_object* v___x_1596_ = _args[6];
lean_object* v___x_1597_ = _args[7];
lean_object* v_result_1598_ = _args[8];
lean_object* v___y_1599_ = _args[9];
lean_object* v___y_1600_ = _args[10];
lean_object* v___y_1601_ = _args[11];
lean_object* v___y_1602_ = _args[12];
lean_object* v___y_1603_ = _args[13];
lean_object* v___y_1604_ = _args[14];
lean_object* v___y_1605_ = _args[15];
lean_object* v___y_1606_ = _args[16];
_start:
{
uint8_t v___x_43948__boxed_1607_; uint8_t v___x_43949__boxed_1608_; lean_object* v_res_1609_; 
v___x_43948__boxed_1607_ = lean_unbox(v___x_1590_);
v___x_43949__boxed_1608_ = lean_unbox(v___x_1594_);
v_res_1609_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_43948__boxed_1607_, v_fvarId_1591_, v_k_1592_, v_args_1593_, v___x_43949__boxed_1608_, v___x_1595_, v___x_1596_, v___x_1597_, v_result_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1610_, lean_object* v_k_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_fvarId_1620_; lean_object* v_value_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1961_; 
v_fvarId_1620_ = lean_ctor_get(v_letDecl_1610_, 0);
v_value_1621_ = lean_ctor_get(v_letDecl_1610_, 3);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_letDecl_1610_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; lean_object* v_unused_1963_; 
v_unused_1962_ = lean_ctor_get(v_letDecl_1610_, 2);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_letDecl_1610_, 1);
lean_dec(v_unused_1963_);
v___x_1623_ = v_letDecl_1610_;
v_isShared_1624_ = v_isSharedCheck_1961_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_value_1621_);
lean_inc(v_fvarId_1620_);
lean_dec(v_letDecl_1610_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1961_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; 
lean_inc(v_value_1621_);
v___x_1625_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1621_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1952_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1952_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1952_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
if (lean_obj_tag(v_a_1626_) == 1)
{
lean_object* v_val_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1628_);
v_val_1630_ = lean_ctor_get(v_a_1626_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_a_1626_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1632_ = v_a_1626_;
v_isShared_1633_ = v_isSharedCheck_1947_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v_a_1626_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1947_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_params_1634_; lean_object* v_value_1635_; lean_object* v_fType_1636_; lean_object* v_args_1637_; uint8_t v_recursive_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; uint8_t v___y_1654_; lean_object* v___y_1655_; uint8_t v___x_1823_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; 
v_params_1634_ = lean_ctor_get(v_val_1630_, 0);
v_value_1635_ = lean_ctor_get(v_val_1630_, 1);
v_fType_1636_ = lean_ctor_get(v_val_1630_, 2);
v_args_1637_ = lean_ctor_get(v_val_1630_, 3);
v_recursive_1638_ = lean_ctor_get_uint8(v_val_1630_, sizeof(void*)*4 + 2);
v___x_1639_ = lean_array_get_size(v_args_1637_);
v___x_1640_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1630_);
v___x_1641_ = lean_nat_dec_lt(v___x_1639_, v___x_1640_);
v___x_1823_ = lean_nat_dec_lt(v___x_1640_, v___x_1639_);
if (lean_obj_tag(v_value_1621_) == 3)
{
lean_object* v_declName_1927_; lean_object* v___x_1928_; 
v_declName_1927_ = lean_ctor_get(v_value_1621_, 0);
lean_inc_n(v_declName_1927_, 2);
lean_dec_ref_known(v_value_1621_, 3);
v___x_1928_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1638_, v_declName_1927_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v_declName_1930_; lean_object* v_config_1931_; lean_object* v_inlineStack_1932_; lean_object* v_inlineStackOccs_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v_declName_1930_ = lean_ctor_get(v_a_1612_, 0);
v_config_1931_ = lean_ctor_get(v_a_1612_, 1);
v_inlineStack_1932_ = lean_ctor_get(v_a_1612_, 2);
v_inlineStackOccs_1933_ = lean_ctor_get(v_a_1612_, 3);
lean_inc(v_inlineStack_1932_);
lean_inc(v_declName_1927_);
v___x_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_declName_1927_);
lean_ctor_set(v___x_1934_, 1, v_inlineStack_1932_);
lean_inc_ref(v_inlineStackOccs_1933_);
v___x_1935_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1933_, v_declName_1927_, v_a_1929_);
lean_inc_ref(v_config_1931_);
lean_inc(v_declName_1930_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 3, v___x_1935_);
lean_ctor_set(v___x_1623_, 2, v___x_1934_);
lean_ctor_set(v___x_1623_, 1, v_config_1931_);
lean_ctor_set(v___x_1623_, 0, v_declName_1930_);
v___x_1937_ = v___x_1623_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_declName_1930_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_config_1931_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v___y_1825_ = v___x_1937_;
v___y_1826_ = v_a_1613_;
v___y_1827_ = v_a_1614_;
v___y_1828_ = v_a_1615_;
v___y_1829_ = v_a_1616_;
v___y_1830_ = v_a_1617_;
v___y_1831_ = v_a_1618_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_declName_1927_);
lean_dec(v___x_1640_);
lean_del_object(v___x_1632_);
lean_dec(v_val_1630_);
lean_del_object(v___x_1623_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
v_a_1939_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1928_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1928_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_del_object(v___x_1623_);
lean_dec(v_value_1621_);
lean_inc_ref(v_a_1612_);
v___y_1825_ = v_a_1612_;
v___y_1826_ = v_a_1613_;
v___y_1827_ = v_a_1614_;
v___y_1828_ = v_a_1615_;
v___y_1829_ = v_a_1616_;
v___y_1830_ = v_a_1617_;
v___y_1831_ = v_a_1618_;
goto v___jp_1824_;
}
v___jp_1642_:
{
lean_object* v___x_1656_; 
lean_inc_ref(v___y_1650_);
v___x_1656_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1651_, v___y_1647_, v___y_1643_, v___y_1646_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1643_);
if (lean_obj_tag(v___x_1658_) == 0)
{
uint8_t v___x_1659_; 
lean_dec_ref_known(v___x_1658_, 1);
v___x_1659_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1657_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec_ref(v___y_1648_);
v___x_1660_ = lean_mk_empty_array_with_capacity(v___y_1644_);
lean_dec(v___y_1644_);
lean_inc_ref(v___x_1660_);
v___x_1661_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1645_, v___x_1660_);
v___x_1662_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1654_, v_fType_1636_, v___x_1661_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc_n(v_a_1663_, 2);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1664_ = l_Lean_Expr_headBeta(v_a_1663_);
v___x_1665_ = l_Lean_Expr_isForall(v___x_1664_);
lean_dec_ref(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref(v___x_1660_);
v___x_1666_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1654_, v_a_1663_, v___x_1641_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_fvarId_1668_; lean_object* v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_fvarId_1668_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1649_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1643_);
lean_inc(v_fvarId_1668_);
v___x_1669_ = lean_apply_9(v___y_1653_, v_fvarId_1668_, v___y_1647_, v___y_1643_, v___y_1646_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_, lean_box(0));
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_mk_empty_array_with_capacity(v___x_1671_);
v___x_1673_ = lean_array_push(v___x_1672_, v_a_1667_);
v___x_1674_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1675_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1654_, v___x_1673_, v_a_1670_, v___x_1674_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_n(v_a_1676_, 2);
lean_dec_ref_known(v___x_1675_, 1);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1677_, 0, v_a_1676_);
lean_closure_set(v___f_1677_, 1, v___x_1671_);
v___x_1678_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1654_, v_a_1657_, v___f_1677_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1690_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_a_1676_);
lean_ctor_set(v___x_1683_, 1, v_a_1679_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1683_);
v___x_1685_ = v___x_1632_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1685_);
v___x_1687_ = v___x_1681_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1676_);
lean_del_object(v___x_1632_);
v_a_1691_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1678_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1678_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1657_);
lean_del_object(v___x_1632_);
v_a_1699_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1675_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1675_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_a_1667_);
lean_dec(v_a_1657_);
lean_del_object(v___x_1632_);
v_a_1707_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1669_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1669_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_a_1657_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1647_);
lean_del_object(v___x_1632_);
v_a_1715_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1666_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1666_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_a_1663_);
v___x_1723_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1724_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1660_, v_a_1657_, v___x_1723_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1725_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v_fvarId_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v_fvarId_1728_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1649_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1647_);
lean_inc(v_fvarId_1728_);
v___x_1729_ = lean_apply_9(v___y_1653_, v_fvarId_1728_, v___y_1647_, v___y_1643_, v___y_1646_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_, lean_box(0));
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1727_);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_mk_empty_array_with_capacity(v___x_1732_);
v___x_1734_ = lean_array_push(v___x_1733_, v___x_1731_);
v___x_1735_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1734_, v_a_1730_, v___y_1647_, v___y_1643_, v___y_1646_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1746_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_a_1736_);
v___x_1741_ = v___x_1632_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1632_);
v_a_1747_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1735_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1735_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1727_);
lean_dec_ref(v___y_1647_);
lean_del_object(v___x_1632_);
v_a_1755_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1729_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1729_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1647_);
lean_del_object(v___x_1632_);
v_a_1763_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1726_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1726_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1647_);
lean_del_object(v___x_1632_);
v_a_1771_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1724_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1724_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___x_1660_);
lean_dec(v_a_1657_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1647_);
lean_del_object(v___x_1632_);
v_a_1779_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1662_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1662_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v___x_1787_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v_fType_1636_);
v___x_1787_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1654_, v_a_1657_, v___y_1648_, v___y_1649_, v___y_1652_, v___y_1650_, v___y_1655_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_a_1788_);
v___x_1793_ = v___x_1632_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
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
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_del_object(v___x_1632_);
v_a_1799_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1787_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1787_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_a_1657_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v_fType_1636_);
lean_del_object(v___x_1632_);
v_a_1807_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1658_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1658_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v_fType_1636_);
lean_del_object(v___x_1632_);
v_a_1815_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1656_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1656_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
v___jp_1824_:
{
if (v___x_1641_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_inc_ref_n(v_args_1637_, 2);
lean_inc_ref(v_fType_1636_);
lean_inc_ref(v_value_1635_);
lean_inc_ref(v_params_1634_);
lean_dec(v_val_1630_);
v___x_1832_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1640_);
v___x_1833_ = l_Array_toSubarray___redArg(v_args_1637_, v___x_1832_, v___x_1640_);
lean_inc_ref(v___x_1833_);
v___x_1834_ = l_Subarray_copy___redArg(v___x_1833_);
v___x_1835_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1634_, v_value_1635_, v___x_1834_, v___x_1641_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec_ref(v_params_1634_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; uint8_t v___x_1842_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = 0;
v___x_1838_ = lean_box(v___x_1823_);
v___x_1839_ = lean_box(v___x_1837_);
lean_inc(v___x_1640_);
lean_inc_ref(v_k_1611_);
lean_inc(v_fvarId_1620_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1840_, 0, v___x_1838_);
lean_closure_set(v___f_1840_, 1, v_fvarId_1620_);
lean_closure_set(v___f_1840_, 2, v_k_1611_);
lean_closure_set(v___f_1840_, 3, v_args_1637_);
lean_closure_set(v___f_1840_, 4, v___x_1839_);
lean_closure_set(v___f_1840_, 5, v___x_1640_);
lean_closure_set(v___f_1840_, 6, v___x_1832_);
lean_closure_set(v___f_1840_, 7, v___x_1639_);
lean_inc_ref(v___y_1827_);
lean_inc_ref(v___y_1825_);
lean_inc_ref(v___f_1840_);
lean_inc(v___y_1826_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1841_, 0, v___y_1826_);
lean_closure_set(v___f_1841_, 1, v___f_1840_);
lean_closure_set(v___f_1841_, 2, v___y_1825_);
lean_closure_set(v___f_1841_, 3, v___y_1827_);
v___x_1842_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1611_, v_fvarId_1620_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
if (v___x_1842_ == 0)
{
lean_dec(v___x_1640_);
v___y_1643_ = v___y_1826_;
v___y_1644_ = v___x_1832_;
v___y_1645_ = v___x_1833_;
v___y_1646_ = v___y_1827_;
v___y_1647_ = v___y_1825_;
v___y_1648_ = v___f_1841_;
v___y_1649_ = v___y_1828_;
v___y_1650_ = v___y_1830_;
v___y_1651_ = v_a_1836_;
v___y_1652_ = v___y_1829_;
v___y_1653_ = v___f_1840_;
v___y_1654_ = v___x_1837_;
v___y_1655_ = v___y_1831_;
goto v___jp_1642_;
}
else
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_eq(v___x_1639_, v___x_1640_);
lean_dec(v___x_1640_);
if (v___x_1843_ == 0)
{
v___y_1643_ = v___y_1826_;
v___y_1644_ = v___x_1832_;
v___y_1645_ = v___x_1833_;
v___y_1646_ = v___y_1827_;
v___y_1647_ = v___y_1825_;
v___y_1648_ = v___f_1841_;
v___y_1649_ = v___y_1828_;
v___y_1650_ = v___y_1830_;
v___y_1651_ = v_a_1836_;
v___y_1652_ = v___y_1829_;
v___y_1653_ = v___f_1840_;
v___y_1654_ = v___x_1837_;
v___y_1655_ = v___y_1831_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref(v___f_1841_);
lean_dec_ref(v___f_1840_);
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_fType_1636_);
lean_del_object(v___x_1632_);
v___x_1844_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1826_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1844_, 1);
lean_inc_ref(v___y_1830_);
v___x_1845_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1836_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec_ref(v___y_1825_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_a_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_a_1855_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1845_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1845_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___y_1825_);
v_a_1863_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1844_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1844_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v___y_1825_);
lean_dec(v___x_1640_);
lean_dec_ref(v_args_1637_);
lean_dec_ref(v_fType_1636_);
lean_del_object(v___x_1632_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
v_a_1871_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1835_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1835_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v___x_1879_; 
lean_dec(v___x_1640_);
lean_del_object(v___x_1632_);
v___x_1879_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1630_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v_fvarId_1881_; lean_object* v___x_1882_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v_fvarId_1881_ = lean_ctor_get(v_a_1880_, 0);
lean_inc(v_fvarId_1881_);
v___x_1882_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1620_, v_fvarId_1881_, v___y_1826_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref_known(v___x_1882_, 1);
v___x_1883_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1826_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref_known(v___x_1883_, 1);
v___x_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_a_1880_);
lean_ctor_set(v___x_1884_, 1, v_k_1611_);
lean_inc_ref(v___y_1830_);
v___x_1885_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1884_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec_ref(v___y_1825_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_a_1886_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1885_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1885_);
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
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1880_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_k_1611_);
v_a_1903_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1883_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1883_);
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
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1880_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_k_1611_);
v_a_1911_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1882_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1882_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___y_1825_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
v_a_1919_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1879_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1879_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_dec(v_a_1626_);
lean_del_object(v___x_1623_);
lean_dec(v_value_1621_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
v___x_1948_ = lean_box(0);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1948_);
v___x_1950_ = v___x_1628_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1623_);
lean_dec(v_value_1621_);
lean_dec(v_fvarId_1620_);
lean_dec_ref(v_k_1611_);
v_a_1953_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1625_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1625_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_typeName_1977_; lean_object* v_discr_1978_; uint8_t v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_subst_1983_; lean_object* v___x_1984_; 
v_typeName_1977_ = lean_ctor_get(v_cases_1965_, 0);
v_discr_1978_ = lean_ctor_get(v_cases_1965_, 2);
v___x_1979_ = 0;
v___x_1980_ = 0;
v___x_1981_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_1982_ = lean_st_ref_get(v_a_1967_);
v_subst_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc_ref(v_subst_1983_);
lean_dec(v___x_1982_);
lean_inc(v_discr_1978_);
v___x_1984_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1983_, v_discr_1978_, v___x_1980_);
lean_dec_ref(v_subst_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_fvarId_1985_; lean_object* v___x_1986_; 
v_fvarId_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_fvarId_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1985_, v_a_1968_, v_a_1970_, v_a_1972_);
lean_dec(v_fvarId_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2215_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_2215_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2215_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
if (lean_obj_tag(v_a_1987_) == 1)
{
lean_object* v_val_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2210_; 
v_val_1991_ = lean_ctor_get(v_a_1987_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_a_1987_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_1993_ = v_a_1987_;
v_isShared_1994_ = v_isSharedCheck_2210_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_val_1991_);
lean_dec(v_a_1987_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2210_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v_env_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_st_ref_get(v_a_1972_);
v_env_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_env_1996_);
lean_dec(v___x_1995_);
v___x_1997_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1991_);
lean_inc(v___x_1997_);
v___x_1998_ = l_Lean_Environment_find_x3f(v_env_1996_, v___x_1997_, v___x_1980_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2209_; 
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2209_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2209_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
if (lean_obj_tag(v_val_1999_) == 6)
{
lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2208_; 
v_val_2003_ = lean_ctor_get(v_val_1999_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_val_1999_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2005_ = v_val_1999_;
v_isShared_2006_ = v_isSharedCheck_2208_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_dec(v_val_1999_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2208_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_induct_2007_; uint8_t v___x_2008_; 
v_induct_2007_ = lean_ctor_get(v_val_2003_, 1);
lean_inc(v_induct_2007_);
lean_dec_ref(v_val_2003_);
v___x_2008_ = lean_name_eq(v_typeName_1977_, v_induct_2007_);
lean_dec(v_induct_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_del_object(v___x_2005_);
lean_del_object(v___x_2001_);
lean_dec(v___x_1997_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
lean_dec_ref(v_cases_1965_);
v___x_2009_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2009_);
v___x_2011_ = v___x_1989_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_1989_);
v___x_2013_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1979_, v_cases_1965_, v___x_1997_);
v_fst_2014_ = lean_ctor_get(v___x_2013_, 0);
v_snd_2015_ = lean_ctor_get(v___x_2013_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2017_ = v___x_2013_;
v_isShared_2018_ = v_isSharedCheck_2207_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v___x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2207_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 4);
lean_ctor_set(v___x_2005_, 0, v_snd_2015_);
v___x_2020_ = v___x_2005_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_snd_2015_);
v___x_2020_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1979_, v___x_2020_, v_a_1970_);
lean_dec_ref(v___x_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; 
lean_dec_ref_known(v___x_2021_, 1);
v___x_2022_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1967_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref_known(v___x_2022_, 1);
if (lean_obj_tag(v_fst_2014_) == 0)
{
if (lean_obj_tag(v_val_1991_) == 0)
{
lean_object* v_params_2023_; lean_object* v_code_2024_; lean_object* v_val_2025_; lean_object* v_args_2026_; lean_object* v_lower_2028_; lean_object* v_upper_2029_; lean_object* v_numParams_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
lean_del_object(v___x_2017_);
lean_del_object(v___x_1993_);
v_params_2023_ = lean_ctor_get(v_fst_2014_, 1);
lean_inc_ref(v_params_2023_);
v_code_2024_ = lean_ctor_get(v_fst_2014_, 2);
lean_inc_ref(v_code_2024_);
lean_dec_ref_known(v_fst_2014_, 3);
v_val_2025_ = lean_ctor_get(v_val_1991_, 0);
lean_inc_ref(v_val_2025_);
v_args_2026_ = lean_ctor_get(v_val_1991_, 1);
lean_inc_ref(v_args_2026_);
lean_dec_ref_known(v_val_1991_, 2);
v_numParams_2072_ = lean_ctor_get(v_val_2025_, 3);
lean_inc(v_numParams_2072_);
lean_dec_ref(v_val_2025_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_array_get_size(v_args_2026_);
v___x_2075_ = lean_nat_dec_le(v_numParams_2072_, v___x_2073_);
if (v___x_2075_ == 0)
{
v_lower_2028_ = v_numParams_2072_;
v_upper_2029_ = v___x_2074_;
goto v___jp_2027_;
}
else
{
lean_dec(v_numParams_2072_);
v_lower_2028_ = v___x_2073_;
v_upper_2029_ = v___x_2074_;
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v___x_2030_; size_t v_sz_2031_; size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = l_Array_toSubarray___redArg(v_args_2026_, v_lower_2028_, v_upper_2029_);
v_sz_2031_ = lean_array_size(v_params_2023_);
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2023_, v_sz_2031_, v___x_2032_, v___x_2030_, v_a_1967_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref_known(v___x_2033_, 1);
lean_inc_ref(v_a_1971_);
v___x_2034_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2024_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1979_, v_params_2023_, v_a_1970_);
lean_dec_ref(v_params_2023_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2047_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2035_);
v___x_2041_ = v___x_2001_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2035_);
v___x_2041_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2041_);
v___x_2043_ = v___x_2038_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_2035_);
lean_del_object(v___x_2001_);
v_a_2048_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2036_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2036_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_params_2023_);
lean_del_object(v___x_2001_);
v_a_2056_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2034_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2034_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_code_2024_);
lean_dec_ref(v_params_2023_);
lean_del_object(v___x_2001_);
v_a_2064_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2033_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2033_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
else
{
lean_object* v_params_2076_; lean_object* v_code_2077_; lean_object* v_n_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2168_; 
v_params_2076_ = lean_ctor_get(v_fst_2014_, 1);
lean_inc_ref(v_params_2076_);
v_code_2077_ = lean_ctor_get(v_fst_2014_, 2);
lean_inc_ref(v_code_2077_);
lean_dec_ref_known(v_fst_2014_, 3);
v_n_2078_ = lean_ctor_get(v_val_1991_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_val_1991_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2080_ = v_val_1991_;
v_isShared_2081_ = v_isSharedCheck_2168_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_n_2078_);
lean_dec(v_val_1991_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2168_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_zero_2082_; uint8_t v_isZero_2083_; 
v_zero_2082_ = lean_unsigned_to_nat(0u);
v_isZero_2083_ = lean_nat_dec_eq(v_n_2078_, v_zero_2082_);
if (v_isZero_2083_ == 1)
{
lean_object* v___x_2084_; 
lean_del_object(v___x_2080_);
lean_dec(v_n_2078_);
lean_dec_ref(v_params_2076_);
lean_del_object(v___x_2017_);
lean_del_object(v___x_1993_);
lean_inc_ref(v_a_1971_);
v___x_2084_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2077_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2095_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2085_);
v___x_2090_ = v___x_2001_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2090_);
v___x_2092_ = v___x_2087_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
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
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_del_object(v___x_2001_);
v_a_2096_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2084_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2084_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_one_2104_; lean_object* v_n_2105_; lean_object* v___x_2107_; 
v_one_2104_ = lean_unsigned_to_nat(1u);
v_n_2105_ = lean_nat_sub(v_n_2078_, v_one_2104_);
lean_dec(v_n_2078_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 0);
lean_ctor_set(v___x_2080_, 0, v_n_2105_);
v___x_2107_ = v___x_2080_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_n_2105_);
v___x_2107_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
lean_ctor_set(v___x_1993_, 0, v___x_2107_);
v___x_2109_ = v___x_1993_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2111_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1979_, v___x_2109_, v___x_2110_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; lean_object* v_fvarId_2114_; lean_object* v_fvarId_2115_; lean_object* v___x_2116_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = lean_array_get_borrowed(v___x_1981_, v_params_2076_, v_zero_2082_);
v_fvarId_2114_ = lean_ctor_get(v___x_2113_, 0);
v_fvarId_2115_ = lean_ctor_get(v_a_2112_, 0);
lean_inc(v_fvarId_2115_);
lean_inc(v_fvarId_2114_);
v___x_2116_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2114_, v_fvarId_2115_, v_a_1967_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2116_, 1);
lean_inc_ref(v_a_1971_);
v___x_2117_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2077_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1979_, v_params_2076_, v_a_1970_);
lean_dec_ref(v_params_2076_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2132_; 
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2133_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2132_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2132_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v_a_2118_);
lean_ctor_set(v___x_2017_, 0, v_a_2112_);
v___x_2124_ = v___x_2017_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2118_);
v___x_2124_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2124_);
v___x_2126_ = v___x_2001_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2128_ = v___x_2121_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2118_);
lean_dec(v_a_2112_);
lean_del_object(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2134_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2119_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2119_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_params_2076_);
lean_del_object(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2142_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2117_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2117_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_code_2077_);
lean_dec_ref(v_params_2076_);
lean_del_object(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2150_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2116_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2116_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_code_2077_);
lean_dec_ref(v_params_2076_);
lean_del_object(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2158_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2111_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2111_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
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
lean_object* v_code_2169_; lean_object* v___x_2170_; 
lean_del_object(v___x_2017_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
v_code_2169_ = lean_ctor_get(v_fst_2014_, 0);
lean_inc_ref(v_code_2169_);
lean_dec_ref_known(v_fst_2014_, 1);
lean_inc_ref(v_a_1971_);
v___x_2170_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2169_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2181_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2181_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2181_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2171_);
v___x_2176_ = v___x_2001_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2178_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2176_);
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2001_);
v_a_2182_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2170_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2170_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_2017_);
lean_dec(v_fst_2014_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
v_a_2190_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2022_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2022_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2017_);
lean_dec(v_fst_2014_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
v_a_2198_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2021_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2021_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
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
lean_del_object(v___x_2001_);
lean_dec(v_val_1999_);
lean_dec(v___x_1997_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_cases_1965_);
goto v___jp_1974_;
}
}
}
else
{
lean_dec(v___x_1998_);
lean_dec(v___x_1997_);
lean_del_object(v___x_1993_);
lean_dec(v_val_1991_);
lean_del_object(v___x_1989_);
lean_dec_ref(v_cases_1965_);
goto v___jp_1974_;
}
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_dec(v_a_1987_);
lean_dec_ref(v_cases_1965_);
v___x_2211_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2211_);
v___x_2213_ = v___x_1989_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_cases_1965_);
v_a_2216_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_1986_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_1986_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2224_; 
lean_dec_ref(v_cases_1965_);
v___x_2224_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1979_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2224_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2224_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
v___jp_1974_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2242_, lean_object* v_i_2243_, lean_object* v_as_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_array_get_size(v_as_2244_);
v___x_2254_ = lean_nat_dec_lt(v_i_2243_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_as_2244_);
return v___x_2255_;
}
else
{
lean_object* v_a_2256_; lean_object* v_a_2258_; 
v_a_2256_ = lean_array_fget_borrowed(v_as_2244_, v_i_2243_);
if (lean_obj_tag(v_a_2256_) == 0)
{
lean_object* v_ctorName_2269_; lean_object* v_params_2270_; lean_object* v_code_2271_; uint8_t v___x_2294_; uint8_t v_a_2296_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_ctorName_2269_ = lean_ctor_get(v_a_2256_, 0);
v_params_2270_ = lean_ctor_get(v_a_2256_, 1);
v_code_2271_ = lean_ctor_get(v_a_2256_, 2);
v___x_2294_ = 0;
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = lean_array_get_size(v_params_2270_);
v___x_2329_ = lean_nat_dec_lt(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
v_a_2296_ = v___x_2329_;
goto v___jp_2295_;
}
else
{
if (v___x_2329_ == 0)
{
v_a_2296_ = v___x_2329_;
goto v___jp_2295_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2328_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2270_, v___x_2330_, v___x_2331_, v___y_2251_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
v_a_2296_ = v___x_2334_;
goto v___jp_2295_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2335_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2332_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2332_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2273_; 
lean_inc_ref(v_params_2270_);
lean_inc(v_ctorName_2269_);
lean_inc(v_fvarId_2242_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2242_, v_ctorName_2269_, v_params_2270_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
lean_inc_ref(v___y_2250_);
lean_inc_ref(v_code_2271_);
v___x_2275_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2271_, v___y_2245_, v___y_2246_, v_a_2274_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v_a_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
lean_inc_ref(v_a_2256_);
v___x_2277_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2256_, v_a_2276_);
v_a_2258_ = v___x_2277_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2278_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2275_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2275_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2286_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2273_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2273_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
v___jp_2295_:
{
if (lean_obj_tag(v_code_2271_) == 6)
{
goto v___jp_2272_;
}
else
{
if (v_a_2296_ == 0)
{
goto v___jp_2272_;
}
else
{
lean_object* v___x_2297_; 
lean_inc_ref(v_code_2271_);
v___x_2297_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2294_, v_code_2271_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2294_, v_code_2271_, v___y_2249_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; 
lean_dec_ref_known(v___x_2299_, 1);
v___x_2300_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2246_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2301_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2298_);
lean_inc_ref(v_a_2256_);
v___x_2302_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2256_, v___x_2301_);
v_a_2258_ = v___x_2302_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2298_);
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2303_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2300_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2300_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
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
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_a_2298_);
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2311_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2299_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2299_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2319_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2297_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2297_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2343_; lean_object* v___x_2344_; 
v_code_2343_ = lean_ctor_get(v_a_2256_, 0);
lean_inc_ref(v___y_2250_);
lean_inc_ref(v_code_2343_);
v___x_2344_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2343_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
lean_inc_ref(v_a_2256_);
v___x_2346_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2256_, v_a_2345_);
v_a_2258_ = v___x_2346_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_as_2244_);
lean_dec(v_i_2243_);
lean_dec(v_fvarId_2242_);
v_a_2347_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2344_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2344_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
v___jp_2257_:
{
size_t v___x_2259_; size_t v___x_2260_; uint8_t v___x_2261_; 
v___x_2259_ = lean_ptr_addr(v_a_2256_);
v___x_2260_ = lean_ptr_addr(v_a_2258_);
v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_i_2243_, v___x_2262_);
v___x_2264_ = lean_array_fset(v_as_2244_, v_i_2243_, v_a_2258_);
lean_dec(v_i_2243_);
v_i_2243_ = v___x_2263_;
v_as_2244_ = v___x_2264_;
goto _start;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v_a_2258_);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_add(v_i_2243_, v___x_2266_);
lean_dec(v_i_2243_);
v_i_2243_ = v___x_2267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2430_; lean_object* v___y_2431_; lean_object* v_decl_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v_decl_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_decl_2502_; lean_object* v_k_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v_decl_2783_; lean_object* v_fvarId_2784_; lean_object* v_type_2785_; lean_object* v_value_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; uint8_t v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2875_; lean_object* v___y_2876_; uint8_t v___y_2877_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v_toCold_3279_; lean_object* v_currRecDepth_3280_; lean_object* v_ref_3281_; uint8_t v_diag_3282_; uint8_t v_suppressElabErrors_3283_; lean_object* v_maxRecDepth_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v_toCold_3279_ = lean_ctor_get(v_a_2362_, 0);
v_currRecDepth_3280_ = lean_ctor_get(v_a_2362_, 1);
v_ref_3281_ = lean_ctor_get(v_a_2362_, 2);
v_diag_3282_ = lean_ctor_get_uint8(v_a_2362_, sizeof(void*)*3);
v_suppressElabErrors_3283_ = lean_ctor_get_uint8(v_a_2362_, sizeof(void*)*3 + 1);
v_maxRecDepth_3313_ = lean_ctor_get(v_toCold_3279_, 3);
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = lean_nat_dec_eq(v_maxRecDepth_3313_, v___x_3314_);
if (v___x_3315_ == 0)
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_nat_dec_eq(v_currRecDepth_3280_, v_maxRecDepth_3313_);
if (v___x_3316_ == 0)
{
lean_inc(v_ref_3281_);
lean_inc(v_currRecDepth_3280_);
lean_inc_ref(v_toCold_3279_);
lean_dec_ref(v_a_2362_);
goto v___jp_3284_;
}
else
{
lean_object* v___x_3317_; 
lean_dec_ref(v_code_2356_);
v___x_3317_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec_ref(v_a_2362_);
return v___x_3317_;
}
}
else
{
lean_inc(v_ref_3281_);
lean_inc(v_currRecDepth_3280_);
lean_inc_ref(v_toCold_3279_);
lean_dec_ref(v_a_2362_);
goto v___jp_3284_;
}
v___jp_2365_:
{
switch(lean_obj_tag(v_code_2356_))
{
case 1:
{
lean_object* v_decl_2368_; lean_object* v_k_2369_; size_t v___x_2370_; size_t v___x_2371_; uint8_t v___x_2372_; 
v_decl_2368_ = lean_ctor_get(v_code_2356_, 0);
v_k_2369_ = lean_ctor_get(v_code_2356_, 1);
v___x_2370_ = lean_ptr_addr(v_k_2369_);
v___x_2371_ = lean_ptr_addr(v___y_2366_);
v___x_2372_ = lean_usize_dec_eq(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
v_isSharedCheck_2380_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; lean_object* v_unused_2382_; 
v_unused_2381_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2382_);
v___x_2374_ = v_code_2356_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v_code_2356_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 1, v___y_2366_);
lean_ctor_set(v___x_2374_, 0, v___y_2367_);
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___y_2366_);
v___x_2377_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
else
{
size_t v___x_2383_; size_t v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = lean_ptr_addr(v_decl_2368_);
v___x_2384_ = lean_ptr_addr(v___y_2367_);
v___x_2385_ = lean_usize_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; lean_object* v_unused_2395_; 
v_unused_2394_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2395_);
v___x_2387_ = v_code_2356_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v_code_2356_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___y_2366_);
lean_ctor_set(v___x_2387_, 0, v___y_2367_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___y_2366_);
v___x_2390_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v___y_2367_);
lean_dec_ref(v___y_2366_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_code_2356_);
return v___x_2396_;
}
}
}
case 2:
{
lean_object* v_decl_2397_; lean_object* v_k_2398_; size_t v___x_2399_; size_t v___x_2400_; uint8_t v___x_2401_; 
v_decl_2397_ = lean_ctor_get(v_code_2356_, 0);
v_k_2398_ = lean_ctor_get(v_code_2356_, 1);
v___x_2399_ = lean_ptr_addr(v_k_2398_);
v___x_2400_ = lean_ptr_addr(v___y_2366_);
v___x_2401_ = lean_usize_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2409_; 
v_isSharedCheck_2409_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; lean_object* v_unused_2411_; 
v_unused_2410_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2411_);
v___x_2403_ = v_code_2356_;
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v_code_2356_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___y_2366_);
lean_ctor_set(v___x_2403_, 0, v___y_2367_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___y_2366_);
v___x_2406_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
}
else
{
size_t v___x_2412_; size_t v___x_2413_; uint8_t v___x_2414_; 
v___x_2412_ = lean_ptr_addr(v_decl_2397_);
v___x_2413_ = lean_ptr_addr(v___y_2367_);
v___x_2414_ = lean_usize_dec_eq(v___x_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_isSharedCheck_2422_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2423_ = lean_ctor_get(v_code_2356_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_2424_);
v___x_2416_ = v_code_2356_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_dec(v_code_2356_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___y_2366_);
lean_ctor_set(v___x_2416_, 0, v___y_2367_);
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___y_2367_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v___y_2366_);
v___x_2419_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
}
else
{
lean_object* v___x_2425_; 
lean_dec_ref(v___y_2367_);
lean_dec_ref(v___y_2366_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_code_2356_);
return v___x_2425_;
}
}
}
default: 
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec_ref(v_code_2356_);
v___x_2426_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2427_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
}
v___jp_2429_:
{
lean_object* v___x_2440_; 
lean_inc_ref(v___y_2438_);
v___x_2440_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2431_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v_fvarId_2442_; lean_object* v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v_fvarId_2442_ = lean_ctor_get(v_decl_2432_, 0);
v___x_2443_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2442_, v___y_2434_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; uint8_t v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_unbox(v_a_2444_);
lean_dec(v_a_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_code_2356_);
v___x_2446_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2432_, v___y_2434_, v___y_2437_);
lean_dec_ref(v_decl_2432_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2446_, 0);
lean_dec(v_unused_2454_);
v___x_2448_ = v___x_2446_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v___x_2446_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v_a_2441_);
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2441_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_a_2441_);
v_a_2455_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2446_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2446_);
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
else
{
if (v___y_2430_ == 0)
{
lean_dec_ref(v___y_2438_);
v___y_2366_ = v_a_2441_;
v___y_2367_ = v_decl_2432_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2463_; 
lean_inc_ref(v_decl_2432_);
v___x_2463_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec_ref(v___y_2438_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_dec_ref_known(v___x_2463_, 1);
v___y_2366_ = v_a_2441_;
v___y_2367_ = v_decl_2432_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_a_2441_);
lean_dec_ref(v_decl_2432_);
lean_dec_ref(v_code_2356_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_a_2441_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_decl_2432_);
lean_dec_ref(v_code_2356_);
v_a_2472_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2443_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2443_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_decl_2432_);
lean_dec_ref(v_code_2356_);
return v___x_2440_;
}
}
v___jp_2480_:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___y_2430_ = v___y_2481_;
v___y_2431_ = v___y_2482_;
v_decl_2432_ = v_a_2492_;
v___y_2433_ = v___y_2484_;
v___y_2434_ = v___y_2485_;
v___y_2435_ = v___y_2486_;
v___y_2436_ = v___y_2487_;
v___y_2437_ = v___y_2488_;
v___y_2438_ = v___y_2489_;
v___y_2439_ = v___y_2490_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_code_2356_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
v___jp_2501_:
{
lean_object* v_fvarId_2511_; lean_object* v_params_2512_; lean_object* v_type_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v_fvarId_2511_ = lean_ctor_get(v_decl_2502_, 0);
v_params_2512_ = lean_ctor_get(v_decl_2502_, 2);
v_type_2513_ = lean_ctor_get(v_decl_2502_, 3);
v___x_2514_ = 0;
v___x_2515_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2511_, v___y_2505_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; uint8_t v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = lean_unbox(v_a_2516_);
if (v___x_2517_ == 0)
{
uint8_t v___x_2518_; 
v___x_2518_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2356_);
if (v___x_2518_ == 0)
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
v___y_2481_ = v___x_2519_;
v___y_2482_ = v_k_2503_;
v_decl_2483_ = v_decl_2502_;
v___y_2484_ = v___y_2504_;
v___y_2485_ = v___y_2505_;
v___y_2486_ = v___y_2506_;
v___y_2487_ = v___y_2507_;
v___y_2488_ = v___y_2508_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
goto v___jp_2480_;
}
else
{
uint8_t v___x_2520_; 
lean_inc_ref(v_type_2513_);
v___x_2520_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2513_, v_params_2512_);
if (v___x_2520_ == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
v___y_2481_ = v___x_2521_;
v___y_2482_ = v_k_2503_;
v_decl_2483_ = v_decl_2502_;
v___y_2484_ = v___y_2504_;
v___y_2485_ = v___y_2505_;
v___y_2486_ = v___y_2506_;
v___y_2487_ = v___y_2507_;
v___y_2488_ = v___y_2508_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2522_; lean_object* v_subst_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2522_ = lean_st_ref_get(v___y_2505_);
v_subst_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_subst_2523_);
lean_dec(v___x_2522_);
v___x_2524_ = lean_unbox(v_a_2516_);
v___x_2525_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2514_, v___x_2524_, v_decl_2502_, v_subst_2523_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec_ref(v_subst_2523_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2526_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2505_);
if (lean_obj_tag(v___x_2529_) == 0)
{
uint8_t v___x_2530_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
v___y_2481_ = v___x_2530_;
v___y_2482_ = v_k_2503_;
v_decl_2483_ = v_a_2528_;
v___y_2484_ = v___y_2504_;
v___y_2485_ = v___y_2505_;
v___y_2486_ = v___y_2506_;
v___y_2487_ = v___y_2507_;
v___y_2488_ = v___y_2508_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2510_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_a_2528_);
lean_dec(v_a_2516_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_k_2503_);
lean_dec_ref(v_code_2356_);
v_a_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2516_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_k_2503_);
lean_dec_ref(v_code_2356_);
v_a_2539_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2527_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2527_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_a_2516_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_k_2503_);
lean_dec_ref(v_code_2356_);
v_a_2547_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2525_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2525_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
}
else
{
uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v_subst_2557_; lean_object* v___x_2558_; 
v___x_2555_ = 0;
v___x_2556_ = lean_st_ref_get(v___y_2505_);
v_subst_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref(v_subst_2557_);
lean_dec(v___x_2556_);
v___x_2558_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2514_, v___x_2555_, v_decl_2502_, v_subst_2557_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec_ref(v_subst_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
v___y_2430_ = v___x_2560_;
v___y_2431_ = v_k_2503_;
v_decl_2432_ = v_a_2559_;
v___y_2433_ = v___y_2504_;
v___y_2434_ = v___y_2505_;
v___y_2435_ = v___y_2506_;
v___y_2436_ = v___y_2507_;
v___y_2437_ = v___y_2508_;
v___y_2438_ = v___y_2509_;
v___y_2439_ = v___y_2510_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2516_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_k_2503_);
lean_dec_ref(v_code_2356_);
v_a_2561_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2558_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2558_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v___y_2509_);
lean_dec_ref(v_k_2503_);
lean_dec_ref(v_decl_2502_);
lean_dec_ref(v_code_2356_);
v_a_2569_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2515_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2515_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
v___jp_2577_:
{
lean_object* v___x_2588_; 
lean_inc_ref(v___y_2581_);
v___x_2588_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2581_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
if (lean_obj_tag(v_a_2589_) == 1)
{
lean_object* v_val_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_val_2590_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_a_2589_, 1);
v___x_2591_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2587_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref_known(v___x_2591_, 1);
lean_inc_ref(v___y_2582_);
v___x_2592_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2586_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2590_, v_a_2593_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
lean_dec_ref(v___y_2582_);
lean_dec(v_val_2590_);
return v___x_2594_;
}
else
{
lean_dec(v_val_2590_);
lean_dec_ref(v___y_2582_);
return v___x_2592_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_val_2590_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2582_);
v_a_2595_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2591_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2591_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; 
lean_dec(v_a_2589_);
lean_inc_ref(v___y_2581_);
v___x_2603_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2581_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
if (lean_obj_tag(v_a_2604_) == 1)
{
lean_object* v_val_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_val_2605_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v_a_2604_, 1);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_val_2605_);
lean_ctor_set(v___x_2606_, 1, v___y_2586_);
v_code_2356_ = v___x_2606_;
v_a_2357_ = v___y_2579_;
v_a_2358_ = v___y_2587_;
v_a_2359_ = v___y_2583_;
v_a_2360_ = v___y_2578_;
v_a_2361_ = v___y_2584_;
v_a_2362_ = v___y_2582_;
v_a_2363_ = v___y_2580_;
goto _start;
}
else
{
lean_object* v_fvarId_2608_; lean_object* v_value_2609_; lean_object* v___x_2610_; 
lean_dec(v_a_2604_);
v_fvarId_2608_ = lean_ctor_get(v___y_2581_, 0);
v_value_2609_ = lean_ctor_get(v___y_2581_, 3);
v___x_2610_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
if (lean_obj_tag(v_a_2611_) == 1)
{
lean_object* v_val_2612_; lean_object* v___x_2613_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v_code_2356_);
v_val_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_val_2612_);
lean_dec_ref_known(v_a_2611_, 1);
lean_inc(v_fvarId_2608_);
v___x_2613_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2608_, v_val_2612_, v___y_2587_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2613_, 1);
v___x_2614_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2581_, v___y_2587_, v___y_2584_);
lean_dec_ref(v___y_2581_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_dec_ref_known(v___x_2614_, 1);
v_code_2356_ = v___y_2586_;
v_a_2357_ = v___y_2579_;
v_a_2358_ = v___y_2587_;
v_a_2359_ = v___y_2583_;
v_a_2360_ = v___y_2578_;
v_a_2361_ = v___y_2584_;
v_a_2362_ = v___y_2582_;
v_a_2363_ = v___y_2580_;
goto _start;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2582_);
v_a_2616_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
v_a_2624_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2613_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2613_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v___x_2632_; 
lean_dec(v_a_2611_);
lean_inc_ref(v___y_2586_);
lean_inc_ref(v___y_2581_);
v___x_2632_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2581_, v___y_2586_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
if (lean_obj_tag(v_a_2633_) == 1)
{
lean_object* v_val_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v_code_2356_);
v_val_2634_ = lean_ctor_get(v_a_2633_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v_a_2633_, 1);
v___x_2635_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2581_, v___y_2587_, v___y_2584_);
lean_dec_ref(v___y_2581_);
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
lean_ctor_set(v___x_2637_, 0, v_val_2634_);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_val_2634_);
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
lean_dec(v_val_2634_);
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
lean_object* v___x_2652_; 
lean_dec(v_a_2633_);
lean_inc(v_value_2609_);
v___x_2652_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2609_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
if (lean_obj_tag(v_a_2653_) == 1)
{
lean_object* v_val_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v_code_2356_);
v_val_2654_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_val_2654_);
lean_dec_ref_known(v_a_2653_, 1);
v_fst_2655_ = lean_ctor_get(v_val_2654_, 0);
lean_inc(v_fst_2655_);
v_snd_2656_ = lean_ctor_get(v_val_2654_, 1);
lean_inc(v_snd_2656_);
lean_dec(v_val_2654_);
lean_inc(v_fvarId_2608_);
v___x_2657_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2608_, v_snd_2656_, v___y_2587_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2658_; 
lean_dec_ref_known(v___x_2657_, 1);
v___x_2658_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2581_, v___y_2587_, v___y_2584_);
lean_dec_ref(v___y_2581_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; 
lean_dec_ref_known(v___x_2658_, 1);
lean_inc_ref(v___y_2582_);
v___x_2659_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2586_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2655_, v_a_2660_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
lean_dec_ref(v___y_2582_);
lean_dec(v_fst_2655_);
return v___x_2661_;
}
else
{
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2582_);
return v___x_2659_;
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2582_);
v_a_2662_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2658_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2658_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
v_a_2670_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2657_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2657_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_a_2653_);
lean_inc_ref(v___y_2582_);
lean_inc_ref(v___y_2586_);
v___x_2678_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2586_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2608_, v___y_2587_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; uint8_t v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_unbox(v_a_2681_);
lean_dec(v_a_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v_code_2356_);
v___x_2683_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2581_, v___y_2587_, v___y_2584_);
lean_dec_ref(v___y_2581_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v___x_2683_, 0);
lean_dec(v_unused_2691_);
v___x_2685_ = v___x_2683_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v___x_2683_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_a_2679_);
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2679_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2679_);
v_a_2692_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2683_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2683_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v___x_2700_; 
lean_inc_ref(v___y_2581_);
v___x_2700_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2581_, v___y_2579_, v___y_2587_, v___y_2583_, v___y_2578_, v___y_2584_, v___y_2582_, v___y_2580_);
lean_dec_ref(v___y_2582_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2721_; 
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; 
v_unused_2722_ = lean_ctor_get(v___x_2700_, 0);
lean_dec(v_unused_2722_);
v___x_2702_ = v___x_2700_;
v_isShared_2703_ = v_isSharedCheck_2721_;
goto v_resetjp_2701_;
}
else
{
lean_dec(v___x_2700_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2721_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
size_t v___x_2704_; size_t v___x_2705_; uint8_t v___x_2706_; 
v___x_2704_ = lean_ptr_addr(v___y_2586_);
lean_dec_ref(v___y_2586_);
v___x_2705_ = lean_ptr_addr(v_a_2679_);
v___x_2706_ = lean_usize_dec_eq(v___x_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
lean_dec_ref(v___y_2585_);
lean_dec_ref(v_code_2356_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2581_);
lean_ctor_set(v___x_2707_, 1, v_a_2679_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2707_);
v___x_2709_ = v___x_2702_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
else
{
size_t v___x_2711_; size_t v___x_2712_; uint8_t v___x_2713_; 
v___x_2711_ = lean_ptr_addr(v___y_2585_);
lean_dec_ref(v___y_2585_);
v___x_2712_ = lean_ptr_addr(v___y_2581_);
v___x_2713_ = lean_usize_dec_eq(v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_dec_ref(v_code_2356_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___y_2581_);
lean_ctor_set(v___x_2714_, 1, v_a_2679_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2714_);
v___x_2716_ = v___x_2702_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
else
{
lean_object* v___x_2719_; 
lean_dec(v_a_2679_);
lean_dec_ref(v___y_2581_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v_code_2356_);
v___x_2719_ = v___x_2702_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_code_2356_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_a_2679_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2723_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2700_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2700_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2679_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2731_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2680_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2680_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2739_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2652_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2652_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2747_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2632_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2632_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2755_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2610_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2610_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2763_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2603_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2603_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_code_2356_);
v_a_2771_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2588_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2588_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2779_:
{
uint8_t v___x_2794_; 
v___x_2794_ = l_Lean_Expr_isErased(v_type_2785_);
lean_dec_ref(v_type_2785_);
if (v___x_2794_ == 0)
{
lean_dec(v_value_2786_);
lean_dec(v_fvarId_2784_);
v___y_2578_ = v___y_2790_;
v___y_2579_ = v___y_2787_;
v___y_2580_ = v___y_2793_;
v___y_2581_ = v_decl_2783_;
v___y_2582_ = v___y_2792_;
v___y_2583_ = v___y_2789_;
v___y_2584_ = v___y_2791_;
v___y_2585_ = v___y_2782_;
v___y_2586_ = v___y_2781_;
v___y_2587_ = v___y_2788_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = lean_box(1);
v___x_2796_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2780_, v_value_2786_, v___x_2795_);
lean_dec(v_value_2786_);
if (v___x_2796_ == 0)
{
if (v___x_2794_ == 0)
{
lean_dec(v_fvarId_2784_);
v___y_2578_ = v___y_2790_;
v___y_2579_ = v___y_2787_;
v___y_2580_ = v___y_2793_;
v___y_2581_ = v_decl_2783_;
v___y_2582_ = v___y_2792_;
v___y_2583_ = v___y_2789_;
v___y_2584_ = v___y_2791_;
v___y_2585_ = v___y_2782_;
v___y_2586_ = v___y_2781_;
v___y_2587_ = v___y_2788_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_subst_2799_; lean_object* v_used_2800_; lean_object* v_binderRenaming_2801_; lean_object* v_funDeclInfoMap_2802_; uint8_t v_simplified_2803_; lean_object* v_visited_2804_; lean_object* v_inline_2805_; lean_object* v_inlineLocal_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_code_2356_);
v___x_2797_ = lean_box(0);
v___x_2798_ = lean_st_ref_take(v___y_2788_);
v_subst_2799_ = lean_ctor_get(v___x_2798_, 0);
v_used_2800_ = lean_ctor_get(v___x_2798_, 1);
v_binderRenaming_2801_ = lean_ctor_get(v___x_2798_, 2);
v_funDeclInfoMap_2802_ = lean_ctor_get(v___x_2798_, 3);
v_simplified_2803_ = lean_ctor_get_uint8(v___x_2798_, sizeof(void*)*7);
v_visited_2804_ = lean_ctor_get(v___x_2798_, 4);
v_inline_2805_ = lean_ctor_get(v___x_2798_, 5);
v_inlineLocal_2806_ = lean_ctor_get(v___x_2798_, 6);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2808_ = v___x_2798_;
v_isShared_2809_ = v_isSharedCheck_2825_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_inlineLocal_2806_);
lean_inc(v_inline_2805_);
lean_inc(v_visited_2804_);
lean_inc(v_funDeclInfoMap_2802_);
lean_inc(v_binderRenaming_2801_);
lean_inc(v_used_2800_);
lean_inc(v_subst_2799_);
lean_dec(v___x_2798_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2825_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2799_, v_fvarId_2784_, v___x_2797_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_used_2800_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_binderRenaming_2801_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_funDeclInfoMap_2802_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_visited_2804_);
lean_ctor_set(v_reuseFailAlloc_2824_, 5, v_inline_2805_);
lean_ctor_set(v_reuseFailAlloc_2824_, 6, v_inlineLocal_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2824_, sizeof(void*)*7, v_simplified_2803_);
v___x_2812_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_st_ref_put(v___y_2788_, v___x_2812_);
v___x_2814_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2783_, v___y_2788_, v___y_2791_);
lean_dec_ref(v_decl_2783_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
v_code_2356_ = v___y_2781_;
v_a_2357_ = v___y_2787_;
v_a_2358_ = v___y_2788_;
v_a_2359_ = v___y_2789_;
v_a_2360_ = v___y_2790_;
v_a_2361_ = v___y_2791_;
v_a_2362_ = v___y_2792_;
v_a_2363_ = v___y_2793_;
goto _start;
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v___y_2792_);
lean_dec_ref(v___y_2781_);
v_a_2816_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2814_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2814_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_2784_);
v___y_2578_ = v___y_2790_;
v___y_2579_ = v___y_2787_;
v___y_2580_ = v___y_2793_;
v___y_2581_ = v_decl_2783_;
v___y_2582_ = v___y_2792_;
v___y_2583_ = v___y_2789_;
v___y_2584_ = v___y_2791_;
v___y_2585_ = v___y_2782_;
v___y_2586_ = v___y_2781_;
v___y_2587_ = v___y_2788_;
goto v___jp_2577_;
}
}
}
v___jp_2826_:
{
lean_object* v_fvarId_2838_; lean_object* v_type_2839_; lean_object* v_value_2840_; lean_object* v___x_2841_; 
v_fvarId_2838_ = lean_ctor_get(v___y_2828_, 0);
v_type_2839_ = lean_ctor_get(v___y_2828_, 2);
v_value_2840_ = lean_ctor_get(v___y_2828_, 3);
lean_inc(v_value_2840_);
v___x_2841_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2840_, v___y_2831_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
if (lean_obj_tag(v_a_2842_) == 1)
{
lean_object* v_val_2843_; lean_object* v___x_2844_; 
v_val_2843_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v_a_2842_, 1);
v___x_2844_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2832_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref_known(v___x_2844_, 1);
v___x_2845_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2827_, v___y_2828_, v_val_2843_, v___y_2835_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v_fvarId_2847_; lean_object* v_type_2848_; lean_object* v_value_2849_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v_fvarId_2847_ = lean_ctor_get(v_a_2846_, 0);
lean_inc(v_fvarId_2847_);
v_type_2848_ = lean_ctor_get(v_a_2846_, 2);
lean_inc_ref(v_type_2848_);
v_value_2849_ = lean_ctor_get(v_a_2846_, 3);
lean_inc(v_value_2849_);
v___y_2780_ = v___y_2827_;
v___y_2781_ = v___y_2830_;
v___y_2782_ = v___y_2829_;
v_decl_2783_ = v_a_2846_;
v_fvarId_2784_ = v_fvarId_2847_;
v_type_2785_ = v_type_2848_;
v_value_2786_ = v_value_2849_;
v___y_2787_ = v___y_2831_;
v___y_2788_ = v___y_2832_;
v___y_2789_ = v___y_2833_;
v___y_2790_ = v___y_2834_;
v___y_2791_ = v___y_2835_;
v___y_2792_ = v___y_2836_;
v___y_2793_ = v___y_2837_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___y_2836_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v_code_2356_);
v_a_2850_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2845_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2845_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_val_2843_);
lean_dec_ref(v___y_2836_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_code_2356_);
v_a_2858_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2844_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2844_);
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
lean_inc(v_value_2840_);
lean_inc_ref(v_type_2839_);
lean_inc(v_fvarId_2838_);
lean_dec(v_a_2842_);
v___y_2780_ = v___y_2827_;
v___y_2781_ = v___y_2830_;
v___y_2782_ = v___y_2829_;
v_decl_2783_ = v___y_2828_;
v_fvarId_2784_ = v_fvarId_2838_;
v_type_2785_ = v_type_2839_;
v_value_2786_ = v_value_2840_;
v___y_2787_ = v___y_2831_;
v___y_2788_ = v___y_2832_;
v___y_2789_ = v___y_2833_;
v___y_2790_ = v___y_2834_;
v___y_2791_ = v___y_2835_;
v___y_2792_ = v___y_2836_;
v___y_2793_ = v___y_2837_;
goto v___jp_2779_;
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v___y_2836_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_code_2356_);
v_a_2866_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2841_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2841_);
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
v___jp_2874_:
{
if (v___y_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec_ref(v_code_2356_);
v___x_2878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___y_2876_);
lean_ctor_set(v___x_2878_, 1, v___y_2875_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; 
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_code_2356_);
return v___x_2880_;
}
}
v___jp_2881_:
{
uint8_t v___x_2886_; 
v___x_2886_ = l_Lean_instBEqFVarId_beq(v___y_2884_, v___y_2885_);
lean_dec(v___y_2884_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v___y_2883_);
v___y_2875_ = v___y_2882_;
v___y_2876_ = v___y_2885_;
v___y_2877_ = v___x_2886_;
goto v___jp_2874_;
}
else
{
size_t v___x_2887_; size_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_ptr_addr(v___y_2883_);
lean_dec_ref(v___y_2883_);
v___x_2888_ = lean_ptr_addr(v___y_2882_);
v___x_2889_ = lean_usize_dec_eq(v___x_2887_, v___x_2888_);
v___y_2875_ = v___y_2882_;
v___y_2876_ = v___y_2885_;
v___y_2877_ = v___x_2889_;
goto v___jp_2874_;
}
}
v___jp_2890_:
{
if (lean_obj_tag(v___y_2895_) == 0)
{
lean_dec_ref_known(v___y_2895_, 1);
v___y_2882_ = v___y_2891_;
v___y_2883_ = v___y_2892_;
v___y_2884_ = v___y_2894_;
v___y_2885_ = v___y_2893_;
goto v___jp_2881_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v_code_2356_);
v_a_2896_ = lean_ctor_get(v___y_2895_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___y_2895_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___y_2895_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___y_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v___jp_2904_:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2915_; 
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; 
v_unused_2916_ = lean_ctor_get(v___x_2907_, 0);
lean_dec(v_unused_2916_);
v___x_2909_ = v___x_2907_;
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v___x_2907_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___y_2905_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2911_);
v___x_2913_ = v___x_2909_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v___y_2905_);
v_a_2917_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2907_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2907_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2925_:
{
if (lean_obj_tag(v___y_2928_) == 0)
{
lean_dec_ref_known(v___y_2928_, 1);
v___y_2905_ = v___y_2926_;
v___y_2906_ = v___y_2927_;
goto v___jp_2904_;
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v___y_2926_);
v_a_2929_ = lean_ctor_get(v___y_2928_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___y_2928_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___y_2928_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___y_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
v___jp_2937_:
{
uint8_t v___x_2947_; 
v___x_2947_ = lean_nat_dec_lt(v___y_2946_, v___y_2940_);
lean_dec(v___y_2946_);
if (v___x_2947_ == 0)
{
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2938_);
v___y_2905_ = v___y_2941_;
v___y_2906_ = v___y_2942_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_nat_dec_le(v___y_2940_, v___y_2940_);
if (v___x_2949_ == 0)
{
if (v___x_2947_ == 0)
{
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2938_);
v___y_2905_ = v___y_2941_;
v___y_2906_ = v___y_2942_;
goto v___jp_2904_;
}
else
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = lean_usize_of_nat(v___y_2940_);
lean_dec(v___y_2940_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2938_, v___x_2950_, v___x_2951_, v___x_2948_, v___y_2944_, v___y_2939_, v___y_2943_, v___y_2945_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2938_);
v___y_2926_ = v___y_2941_;
v___y_2927_ = v___y_2942_;
v___y_2928_ = v___x_2952_;
goto v___jp_2925_;
}
}
else
{
size_t v___x_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = ((size_t)0ULL);
v___x_2954_ = lean_usize_of_nat(v___y_2940_);
lean_dec(v___y_2940_);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2938_, v___x_2953_, v___x_2954_, v___x_2948_, v___y_2944_, v___y_2939_, v___y_2943_, v___y_2945_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2938_);
v___y_2926_ = v___y_2941_;
v___y_2927_ = v___y_2942_;
v___y_2928_ = v___x_2955_;
goto v___jp_2925_;
}
}
}
v___jp_2956_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2958_);
lean_ctor_set(v___x_2961_, 1, v___y_2959_);
lean_ctor_set(v___x_2961_, 2, v___y_2960_);
lean_ctor_set(v___x_2961_, 3, v___y_2957_);
v___x_2962_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
v___jp_2964_:
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_array_get_size(v___y_2965_);
v___x_2979_ = lean_nat_dec_lt(v___y_2972_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_dec(v___y_2971_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v_code_2356_);
v___y_2938_ = v___y_2965_;
v___y_2939_ = v___y_2975_;
v___y_2940_ = v___x_2978_;
v___y_2941_ = v___y_2970_;
v___y_2942_ = v___y_2973_;
v___y_2943_ = v___y_2976_;
v___y_2944_ = v___y_2974_;
v___y_2945_ = v___y_2977_;
v___y_2946_ = v___y_2972_;
goto v___jp_2937_;
}
else
{
if (v___x_2979_ == 0)
{
lean_dec(v___y_2971_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v_code_2356_);
v___y_2938_ = v___y_2965_;
v___y_2939_ = v___y_2975_;
v___y_2940_ = v___x_2978_;
v___y_2941_ = v___y_2970_;
v___y_2942_ = v___y_2973_;
v___y_2943_ = v___y_2976_;
v___y_2944_ = v___y_2974_;
v___y_2945_ = v___y_2977_;
v___y_2946_ = v___y_2972_;
goto v___jp_2937_;
}
else
{
size_t v___x_2980_; size_t v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = ((size_t)0ULL);
v___x_2981_ = lean_usize_of_nat(v___x_2978_);
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2965_, v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_dec(v___y_2971_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v_code_2356_);
v___y_2938_ = v___y_2965_;
v___y_2939_ = v___y_2975_;
v___y_2940_ = v___x_2978_;
v___y_2941_ = v___y_2970_;
v___y_2942_ = v___y_2973_;
v___y_2943_ = v___y_2976_;
v___y_2944_ = v___y_2974_;
v___y_2945_ = v___y_2977_;
v___y_2946_ = v___y_2972_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2972_);
lean_inc(v___y_2971_);
v___x_2983_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2971_, v___y_2973_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2997_; 
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2983_, 0);
lean_dec(v_unused_2998_);
v___x_2985_ = v___x_2983_;
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v___x_2983_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
size_t v___x_2987_; size_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_ptr_addr(v___y_2967_);
lean_dec_ref(v___y_2967_);
v___x_2988_ = lean_ptr_addr(v___y_2965_);
v___x_2989_ = lean_usize_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_del_object(v___x_2985_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2966_);
lean_dec_ref(v_code_2356_);
v___y_2957_ = v___y_2965_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v___y_2971_;
goto v___jp_2956_;
}
else
{
size_t v___x_2990_; size_t v___x_2991_; uint8_t v___x_2992_; 
v___x_2990_ = lean_ptr_addr(v___y_2968_);
lean_dec_ref(v___y_2968_);
v___x_2991_ = lean_ptr_addr(v___y_2970_);
v___x_2992_ = lean_usize_dec_eq(v___x_2990_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_del_object(v___x_2985_);
lean_dec(v___y_2966_);
lean_dec_ref(v_code_2356_);
v___y_2957_ = v___y_2965_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v___y_2971_;
goto v___jp_2956_;
}
else
{
uint8_t v___x_2993_; 
v___x_2993_ = l_Lean_instBEqFVarId_beq(v___y_2966_, v___y_2971_);
lean_dec(v___y_2966_);
if (v___x_2993_ == 0)
{
lean_del_object(v___x_2985_);
lean_dec_ref(v_code_2356_);
v___y_2957_ = v___y_2965_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v___y_2971_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2995_; 
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2965_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v_code_2356_);
v___x_2995_ = v___x_2985_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_code_2356_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_code_2356_);
v_a_2999_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2983_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2983_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
}
v___jp_3007_:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3008_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_3010_, 0);
lean_dec(v_unused_3018_);
v___x_3012_ = v___x_3010_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_dec(v___x_3010_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___y_3009_);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___y_3009_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v___y_3009_);
v_a_3019_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3010_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3010_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
v___jp_3027_:
{
if (lean_obj_tag(v___y_3030_) == 0)
{
lean_dec_ref_known(v___y_3030_, 1);
v___y_3008_ = v___y_3028_;
v___y_3009_ = v___y_3029_;
goto v___jp_3007_;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___y_3029_);
v_a_3031_ = lean_ctor_get(v___y_3030_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___y_3030_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___y_3030_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___y_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
v___jp_3039_:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_lt(v___y_3045_, v___y_3044_);
lean_dec(v___y_3045_);
if (v___x_3046_ == 0)
{
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3041_);
v___y_3008_ = v___y_3042_;
v___y_3009_ = v___y_3043_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_nat_dec_le(v___y_3044_, v___y_3044_);
if (v___x_3048_ == 0)
{
if (v___x_3046_ == 0)
{
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3041_);
v___y_3008_ = v___y_3042_;
v___y_3009_ = v___y_3043_;
goto v___jp_3007_;
}
else
{
size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = lean_usize_of_nat(v___y_3044_);
lean_dec(v___y_3044_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3041_, v___x_3049_, v___x_3050_, v___x_3047_, v___y_3040_);
lean_dec_ref(v___y_3041_);
v___y_3028_ = v___y_3042_;
v___y_3029_ = v___y_3043_;
v___y_3030_ = v___x_3051_;
goto v___jp_3027_;
}
}
else
{
size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = lean_usize_of_nat(v___y_3044_);
lean_dec(v___y_3044_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3041_, v___x_3052_, v___x_3053_, v___x_3047_, v___y_3040_);
lean_dec_ref(v___y_3041_);
v___y_3028_ = v___y_3042_;
v___y_3029_ = v___y_3043_;
v___y_3030_ = v___x_3054_;
goto v___jp_3027_;
}
}
}
v___jp_3055_:
{
switch(lean_obj_tag(v_code_2356_))
{
case 0:
{
lean_object* v_decl_3063_; lean_object* v_k_3064_; uint8_t v___x_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; 
v_decl_3063_ = lean_ctor_get(v_code_2356_, 0);
v_k_3064_ = lean_ctor_get(v_code_2356_, 1);
v___x_3065_ = 0;
v___x_3066_ = 0;
lean_inc_ref(v_decl_3063_);
v___x_3067_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3065_, v___x_3066_, v_decl_3063_, v___y_3057_, v___y_3060_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; uint8_t v___x_3069_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3065_, v_decl_3063_, v_a_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3057_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_dec_ref_known(v___x_3070_, 1);
lean_inc_ref(v_k_3064_);
lean_inc_ref(v_decl_3063_);
v___y_2827_ = v___x_3065_;
v___y_2828_ = v_a_3068_;
v___y_2829_ = v_decl_3063_;
v___y_2830_ = v_k_3064_;
v___y_2831_ = v___y_3056_;
v___y_2832_ = v___y_3057_;
v___y_2833_ = v___y_3058_;
v___y_2834_ = v___y_3059_;
v___y_2835_ = v___y_3060_;
v___y_2836_ = v___y_3061_;
v___y_2837_ = v___y_3062_;
goto v___jp_2826_;
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_3068_);
lean_dec_ref_known(v_code_2356_, 2);
lean_dec_ref(v___y_3061_);
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_inc_ref(v_k_3064_);
lean_inc_ref(v_decl_3063_);
v___y_2827_ = v___x_3065_;
v___y_2828_ = v_a_3068_;
v___y_2829_ = v_decl_3063_;
v___y_2830_ = v_k_3064_;
v___y_2831_ = v___y_3056_;
v___y_2832_ = v___y_3057_;
v___y_2833_ = v___y_3058_;
v___y_2834_ = v___y_3059_;
v___y_2835_ = v___y_3060_;
v___y_2836_ = v___y_3061_;
v___y_2837_ = v___y_3062_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref_known(v_code_2356_, 2);
lean_dec_ref(v___y_3061_);
v_a_3079_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3067_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3067_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3087_; lean_object* v_args_3088_; uint8_t v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v_subst_3092_; lean_object* v___x_3093_; 
v_fvarId_3087_ = lean_ctor_get(v_code_2356_, 0);
v_args_3088_ = lean_ctor_get(v_code_2356_, 1);
v___x_3089_ = 0;
v___x_3090_ = 0;
v___x_3091_ = lean_st_ref_get(v___y_3057_);
v_subst_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_subst_3092_);
lean_dec(v___x_3091_);
lean_inc(v_fvarId_3087_);
v___x_3093_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3092_, v_fvarId_3087_, v___x_3090_);
lean_dec_ref(v_subst_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_fvarId_3094_; lean_object* v___x_3095_; 
v_fvarId_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_fvarId_3094_);
lean_dec_ref_known(v___x_3093_, 1);
lean_inc_ref(v_args_3088_);
v___x_3095_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3089_, v___x_3090_, v_args_3088_, v___y_3057_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc_n(v_a_3096_, 2);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3094_, v_a_3096_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
if (lean_obj_tag(v_a_3098_) == 1)
{
lean_object* v_val_3099_; 
lean_dec(v_a_3096_);
lean_dec(v_fvarId_3094_);
lean_dec_ref_known(v_code_2356_, 2);
v_val_3099_ = lean_ctor_get(v_a_3098_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v_a_3098_, 1);
v_code_2356_ = v_val_3099_;
v_a_2357_ = v___y_3056_;
v_a_2358_ = v___y_3057_;
v_a_2359_ = v___y_3058_;
v_a_2360_ = v___y_3059_;
v_a_2361_ = v___y_3060_;
v_a_2362_ = v___y_3061_;
v_a_2363_ = v___y_3062_;
goto _start;
}
else
{
lean_object* v___x_3101_; 
lean_dec(v_a_3098_);
lean_dec_ref(v___y_3061_);
lean_inc(v_fvarId_3094_);
v___x_3101_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3094_, v___y_3057_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
lean_dec_ref_known(v___x_3101_, 1);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = lean_array_get_size(v_a_3096_);
v___x_3104_ = lean_nat_dec_lt(v___x_3102_, v___x_3103_);
if (v___x_3104_ == 0)
{
lean_inc(v_fvarId_3087_);
lean_inc_ref(v_args_3088_);
v___y_2882_ = v_a_3096_;
v___y_2883_ = v_args_3088_;
v___y_2884_ = v_fvarId_3087_;
v___y_2885_ = v_fvarId_3094_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3105_ = lean_box(0);
v___x_3106_ = lean_nat_dec_le(v___x_3103_, v___x_3103_);
if (v___x_3106_ == 0)
{
if (v___x_3104_ == 0)
{
lean_inc(v_fvarId_3087_);
lean_inc_ref(v_args_3088_);
v___y_2882_ = v_a_3096_;
v___y_2883_ = v_args_3088_;
v___y_2884_ = v_fvarId_3087_;
v___y_2885_ = v_fvarId_3094_;
goto v___jp_2881_;
}
else
{
size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = lean_usize_of_nat(v___x_3103_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3096_, v___x_3107_, v___x_3108_, v___x_3105_, v___y_3057_);
lean_inc(v_fvarId_3087_);
lean_inc_ref(v_args_3088_);
v___y_2891_ = v_a_3096_;
v___y_2892_ = v_args_3088_;
v___y_2893_ = v_fvarId_3094_;
v___y_2894_ = v_fvarId_3087_;
v___y_2895_ = v___x_3109_;
goto v___jp_2890_;
}
}
else
{
size_t v___x_3110_; size_t v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((size_t)0ULL);
v___x_3111_ = lean_usize_of_nat(v___x_3103_);
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3096_, v___x_3110_, v___x_3111_, v___x_3105_, v___y_3057_);
lean_inc(v_fvarId_3087_);
lean_inc_ref(v_args_3088_);
v___y_2891_ = v_a_3096_;
v___y_2892_ = v_args_3088_;
v___y_2893_ = v_fvarId_3094_;
v___y_2894_ = v_fvarId_3087_;
v___y_2895_ = v___x_3112_;
goto v___jp_2890_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3096_);
lean_dec(v_fvarId_3094_);
lean_dec_ref_known(v_code_2356_, 2);
v_a_3113_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3101_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3101_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3096_);
lean_dec(v_fvarId_3094_);
lean_dec_ref_known(v_code_2356_, 2);
lean_dec_ref(v___y_3061_);
v_a_3121_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3097_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3097_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_fvarId_3094_);
lean_dec_ref_known(v_code_2356_, 2);
lean_dec_ref(v___y_3061_);
v_a_3129_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3095_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3095_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3137_; 
lean_dec_ref_known(v_code_2356_, 2);
v___x_3137_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3089_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec_ref(v___y_3061_);
return v___x_3137_;
}
}
case 4:
{
lean_object* v_cases_3138_; lean_object* v___x_3139_; 
v_cases_3138_ = lean_ctor_get(v_code_2356_, 0);
lean_inc_ref(v_cases_3138_);
v___x_3139_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3138_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3212_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3212_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3212_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
if (lean_obj_tag(v_a_3140_) == 1)
{
lean_object* v_val_3144_; lean_object* v___x_3146_; 
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_val_3144_ = lean_ctor_get(v_a_3140_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v_a_3140_, 1);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_val_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_val_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
else
{
lean_object* v_typeName_3148_; lean_object* v_resultType_3149_; lean_object* v_discr_3150_; lean_object* v_alts_3151_; uint8_t v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v_subst_3155_; lean_object* v___x_3156_; 
lean_del_object(v___x_3142_);
lean_dec(v_a_3140_);
v_typeName_3148_ = lean_ctor_get(v_cases_3138_, 0);
v_resultType_3149_ = lean_ctor_get(v_cases_3138_, 1);
v_discr_3150_ = lean_ctor_get(v_cases_3138_, 2);
v_alts_3151_ = lean_ctor_get(v_cases_3138_, 3);
v___x_3152_ = 0;
v___x_3153_ = 0;
v___x_3154_ = lean_st_ref_get(v___y_3057_);
v_subst_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc_ref(v_subst_3155_);
lean_dec(v___x_3154_);
lean_inc(v_discr_3150_);
v___x_3156_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3155_, v_discr_3150_, v___x_3153_);
lean_dec_ref(v_subst_3155_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_fvarId_3157_; lean_object* v___x_3158_; lean_object* v_subst_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_fvarId_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc_n(v_fvarId_3157_, 2);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = lean_st_ref_get(v___y_3057_);
v_subst_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc_ref(v_subst_3159_);
lean_dec(v___x_3158_);
lean_inc_ref(v_resultType_3149_);
v___x_3160_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3152_, v_subst_3159_, v___x_3153_, v_resultType_3149_);
lean_dec_ref(v_subst_3159_);
v___x_3161_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3151_);
v___x_3162_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3157_, v___x_3161_, v_alts_3151_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3163_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3194_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3194_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3194_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3169_ = lean_array_get_size(v_a_3165_);
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_nat_dec_eq(v___x_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_del_object(v___x_3167_);
lean_inc(v_typeName_3148_);
lean_inc_ref(v_resultType_3149_);
lean_inc_ref(v_alts_3151_);
lean_inc(v_discr_3150_);
v___y_2965_ = v_a_3165_;
v___y_2966_ = v_discr_3150_;
v___y_2967_ = v_alts_3151_;
v___y_2968_ = v_resultType_3149_;
v___y_2969_ = v_typeName_3148_;
v___y_2970_ = v___x_3160_;
v___y_2971_ = v_fvarId_3157_;
v___y_2972_ = v___x_3161_;
v___y_2973_ = v___y_3057_;
v___y_2974_ = v___y_3059_;
v___y_2975_ = v___y_3060_;
v___y_2976_ = v___y_3061_;
v___y_2977_ = v___y_3062_;
goto v___jp_2964_;
}
else
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_array_fget_borrowed(v_a_3165_, v___x_3161_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_params_3173_; lean_object* v_code_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
lean_del_object(v___x_3167_);
v_params_3173_ = lean_ctor_get(v___x_3172_, 1);
v_code_3174_ = lean_ctor_get(v___x_3172_, 2);
v___x_3175_ = lean_array_get_size(v_params_3173_);
v___x_3176_ = lean_nat_dec_lt(v___x_3161_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_inc_ref(v_code_3174_);
lean_inc_ref(v_params_3173_);
lean_dec(v_a_3165_);
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v___y_3040_ = v___y_3060_;
v___y_3041_ = v_params_3173_;
v___y_3042_ = v___y_3057_;
v___y_3043_ = v_code_3174_;
v___y_3044_ = v___x_3175_;
v___y_3045_ = v___x_3161_;
goto v___jp_3039_;
}
else
{
if (v___x_3176_ == 0)
{
lean_inc_ref(v_code_3174_);
lean_inc_ref(v_params_3173_);
lean_dec(v_a_3165_);
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v___y_3040_ = v___y_3060_;
v___y_3041_ = v_params_3173_;
v___y_3042_ = v___y_3057_;
v___y_3043_ = v_code_3174_;
v___y_3044_ = v___x_3175_;
v___y_3045_ = v___x_3161_;
goto v___jp_3039_;
}
else
{
size_t v___x_3177_; size_t v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = lean_usize_of_nat(v___x_3175_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3173_, v___x_3177_, v___x_3178_, v___y_3057_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; uint8_t v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v___x_3181_ = lean_unbox(v_a_3180_);
lean_dec(v_a_3180_);
if (v___x_3181_ == 0)
{
lean_inc_ref(v_code_3174_);
lean_inc_ref(v_params_3173_);
lean_dec(v_a_3165_);
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v___y_3040_ = v___y_3060_;
v___y_3041_ = v_params_3173_;
v___y_3042_ = v___y_3057_;
v___y_3043_ = v_code_3174_;
v___y_3044_ = v___x_3175_;
v___y_3045_ = v___x_3161_;
goto v___jp_3039_;
}
else
{
lean_inc(v_typeName_3148_);
lean_inc_ref(v_resultType_3149_);
lean_inc_ref(v_alts_3151_);
lean_inc(v_discr_3150_);
v___y_2965_ = v_a_3165_;
v___y_2966_ = v_discr_3150_;
v___y_2967_ = v_alts_3151_;
v___y_2968_ = v_resultType_3149_;
v___y_2969_ = v_typeName_3148_;
v___y_2970_ = v___x_3160_;
v___y_2971_ = v_fvarId_3157_;
v___y_2972_ = v___x_3161_;
v___y_2973_ = v___y_3057_;
v___y_2974_ = v___y_3059_;
v___y_2975_ = v___y_3060_;
v___y_2976_ = v___y_3061_;
v___y_2977_ = v___y_3062_;
goto v___jp_2964_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3165_);
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_a_3182_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3179_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3179_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
}
else
{
lean_object* v_code_3190_; lean_object* v___x_3192_; 
lean_inc_ref(v___x_3172_);
lean_dec(v_a_3165_);
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_code_3190_ = lean_ctor_get(v___x_3172_, 0);
lean_inc_ref(v_code_3190_);
lean_dec_ref_known(v___x_3172_, 1);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_code_3190_);
v___x_3192_ = v___x_3167_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_code_3190_);
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
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_a_3195_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3164_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3164_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v___x_3160_);
lean_dec(v_fvarId_3157_);
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_a_3203_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3162_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3162_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v___x_3211_; 
lean_dec_ref_known(v_code_2356_, 1);
v___x_3211_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3152_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec_ref(v___y_3061_);
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref_known(v_code_2356_, 1);
lean_dec_ref(v___y_3061_);
v_a_3213_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3139_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3139_);
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
case 5:
{
lean_object* v_fvarId_3221_; uint8_t v___x_3222_; uint8_t v___x_3223_; lean_object* v___x_3224_; lean_object* v_subst_3225_; lean_object* v___x_3226_; 
v_fvarId_3221_ = lean_ctor_get(v_code_2356_, 0);
v___x_3222_ = 0;
v___x_3223_ = 0;
v___x_3224_ = lean_st_ref_get(v___y_3057_);
v_subst_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_subst_3225_);
lean_dec(v___x_3224_);
lean_inc(v_fvarId_3221_);
v___x_3226_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3225_, v_fvarId_3221_, v___x_3223_);
lean_dec_ref(v_subst_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_fvarId_3227_; lean_object* v___x_3228_; 
lean_dec_ref(v___y_3061_);
v_fvarId_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_n(v_fvarId_3227_, 2);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3227_, v___y_3057_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3247_; 
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3228_, 0);
lean_dec(v_unused_3248_);
v___x_3230_ = v___x_3228_;
v_isShared_3231_ = v_isSharedCheck_3247_;
goto v_resetjp_3229_;
}
else
{
lean_dec(v___x_3228_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3247_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
uint8_t v___x_3232_; 
v___x_3232_ = l_Lean_instBEqFVarId_beq(v_fvarId_3221_, v_fvarId_3227_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3242_; 
v_isSharedCheck_3242_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_3243_);
v___x_3234_ = v_code_2356_;
v_isShared_3235_ = v_isSharedCheck_3242_;
goto v_resetjp_3233_;
}
else
{
lean_dec(v_code_2356_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3242_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_fvarId_3227_);
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_fvarId_3227_);
v___x_3237_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3237_);
v___x_3239_ = v___x_3230_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3245_; 
lean_dec(v_fvarId_3227_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v_code_2356_);
v___x_3245_ = v___x_3230_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_code_2356_);
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
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_fvarId_3227_);
lean_dec_ref_known(v_code_2356_, 1);
v_a_3249_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3228_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3228_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v___x_3257_; 
lean_dec_ref_known(v_code_2356_, 1);
v___x_3257_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3222_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec_ref(v___y_3061_);
return v___x_3257_;
}
}
case 6:
{
lean_object* v_type_3258_; uint8_t v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v_subst_3262_; lean_object* v___x_3263_; size_t v___x_3264_; size_t v___x_3265_; uint8_t v___x_3266_; 
lean_dec_ref(v___y_3061_);
v_type_3258_ = lean_ctor_get(v_code_2356_, 0);
v___x_3259_ = 0;
v___x_3260_ = 0;
v___x_3261_ = lean_st_ref_get(v___y_3057_);
v_subst_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc_ref(v_subst_3262_);
lean_dec(v___x_3261_);
lean_inc_ref(v_type_3258_);
v___x_3263_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3259_, v_subst_3262_, v___x_3260_, v_type_3258_);
lean_dec_ref(v_subst_3262_);
v___x_3264_ = lean_ptr_addr(v_type_3258_);
v___x_3265_ = lean_ptr_addr(v___x_3263_);
v___x_3266_ = lean_usize_dec_eq(v___x_3264_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3274_; 
v_isSharedCheck_3274_ = !lean_is_exclusive(v_code_2356_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v_code_2356_, 0);
lean_dec(v_unused_3275_);
v___x_3268_ = v_code_2356_;
v_isShared_3269_ = v_isSharedCheck_3274_;
goto v_resetjp_3267_;
}
else
{
lean_dec(v_code_2356_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3274_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3263_);
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3263_);
v___x_3271_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
}
}
else
{
lean_object* v___x_3276_; 
lean_dec_ref(v___x_3263_);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_code_2356_);
return v___x_3276_;
}
}
default: 
{
lean_object* v_decl_3277_; lean_object* v_k_3278_; 
v_decl_3277_ = lean_ctor_get(v_code_2356_, 0);
v_k_3278_ = lean_ctor_get(v_code_2356_, 1);
lean_inc_ref(v_k_3278_);
lean_inc_ref(v_decl_3277_);
v_decl_2502_ = v_decl_3277_;
v_k_2503_ = v_k_3278_;
v___y_2504_ = v___y_3056_;
v___y_2505_ = v___y_3057_;
v___y_2506_ = v___y_3058_;
v___y_2507_ = v___y_3059_;
v___y_2508_ = v___y_3060_;
v___y_2509_ = v___y_3061_;
v___y_2510_ = v___y_3062_;
goto v___jp_2501_;
}
}
}
v___jp_3284_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_nat_add(v_currRecDepth_3280_, v___x_3285_);
lean_dec(v_currRecDepth_3280_);
v___x_3287_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3287_, 0, v_toCold_3279_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
lean_ctor_set(v___x_3287_, 2, v_ref_3281_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*3, v_diag_3282_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*3 + 1, v_suppressElabErrors_3283_);
v___x_3288_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2358_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v___x_3289_; lean_object* v_visited_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
lean_dec_ref_known(v___x_3288_, 1);
v___x_3289_ = lean_st_ref_get(v_a_2358_);
v_visited_3290_ = lean_ctor_get(v___x_3289_, 4);
lean_inc(v_visited_3290_);
lean_dec(v___x_3289_);
v___x_3291_ = lean_unsigned_to_nat(128u);
v___x_3292_ = lean_nat_mod(v_visited_3290_, v___x_3291_);
lean_dec(v_visited_3290_);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_nat_dec_eq(v___x_3292_, v___x_3293_);
lean_dec(v___x_3292_);
if (v___x_3294_ == 0)
{
v___y_3056_ = v_a_2357_;
v___y_3057_ = v_a_2358_;
v___y_3058_ = v_a_2359_;
v___y_3059_ = v_a_2360_;
v___y_3060_ = v_a_2361_;
v___y_3061_ = v___x_3287_;
v___y_3062_ = v_a_2363_;
goto v___jp_3055_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3296_ = l_Lean_Core_checkSystem(v___x_3295_, v___x_3287_, v_a_2363_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref_known(v___x_3296_, 1);
v___y_3056_ = v_a_2357_;
v___y_3057_ = v_a_2358_;
v___y_3058_ = v_a_2359_;
v___y_3059_ = v_a_2360_;
v___y_3060_ = v_a_2361_;
v___y_3061_ = v___x_3287_;
v___y_3062_ = v_a_2363_;
goto v___jp_3055_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref_known(v___x_3287_, 3);
lean_dec_ref(v_code_2356_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref_known(v___x_3287_, 3);
lean_dec_ref(v_code_2356_);
v_a_3305_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3288_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3288_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_params_3327_; lean_object* v_type_3328_; lean_object* v_value_3329_; uint8_t v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v_subst_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_params_3327_ = lean_ctor_get(v_decl_3318_, 2);
v_type_3328_ = lean_ctor_get(v_decl_3318_, 3);
v_value_3329_ = lean_ctor_get(v_decl_3318_, 4);
v___x_3330_ = 0;
v___x_3331_ = 0;
v___x_3332_ = lean_st_ref_get(v_a_3320_);
v_subst_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc_ref(v_subst_3333_);
lean_dec(v___x_3332_);
lean_inc_ref(v_type_3328_);
v___x_3334_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3330_, v_subst_3333_, v___x_3331_, v_type_3328_);
lean_dec_ref(v_subst_3333_);
lean_inc_ref(v_params_3327_);
v___x_3335_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3330_, v___x_3331_, v_params_3327_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
lean_inc_ref(v_a_3324_);
lean_inc_ref(v_value_3329_);
v___x_3337_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3329_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3330_, v_decl_3318_, v___x_3334_, v_a_3336_, v_a_3338_, v_a_3323_);
return v___x_3339_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_a_3336_);
lean_dec_ref(v___x_3334_);
lean_dec_ref(v_decl_3318_);
v_a_3340_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3337_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3337_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___x_3334_);
lean_dec_ref(v_decl_3318_);
v_a_3348_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3335_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3335_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3366_, lean_object* v_i_3367_, lean_object* v_as_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3366_, v_i_3367_, v_as_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3388_, lean_object* v_k_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3388_, v_k_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3409_, uint8_t v_t_3410_, lean_object* v_decl_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3409_, v_t_3410_, v_decl_3411_, v___y_3413_, v___y_3416_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3421_, lean_object* v_t_3422_, lean_object* v_decl_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v_pu_boxed_3432_; uint8_t v_t_boxed_3433_; lean_object* v_res_3434_; 
v_pu_boxed_3432_ = lean_unbox(v_pu_3421_);
v_t_boxed_3433_ = lean_unbox(v_t_3422_);
v_res_3434_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3432_, v_t_boxed_3433_, v_decl_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3435_, uint8_t v_t_3436_, lean_object* v_args_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3435_, v_t_3436_, v_args_3437_, v___y_3439_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3447_, lean_object* v_t_3448_, lean_object* v_args_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v_pu_boxed_3458_; uint8_t v_t_boxed_3459_; lean_object* v_res_3460_; 
v_pu_boxed_3458_ = lean_unbox(v_pu_3447_);
v_t_boxed_3459_ = lean_unbox(v_t_3448_);
v_res_3460_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3458_, v_t_boxed_3459_, v_args_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3461_, lean_object* v_R_3462_, lean_object* v_a_3463_, lean_object* v_b_3464_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3463_, v_b_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3466_, lean_object* v_x_3467_, lean_object* v_x_3468_, lean_object* v_x_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3467_, v_x_3468_, v_x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3471_, size_t v_i_3472_, size_t v_stop_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3471_, v_i_3472_, v_stop_3473_, v_b_3474_, v___y_3476_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3484_, lean_object* v_i_3485_, lean_object* v_stop_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
size_t v_i_boxed_3496_; size_t v_stop_boxed_3497_; lean_object* v_res_3498_; 
v_i_boxed_3496_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_stop_boxed_3497_ = lean_unbox_usize(v_stop_3486_);
lean_dec(v_stop_3486_);
v_res_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3484_, v_i_boxed_3496_, v_stop_boxed_3497_, v_b_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_as_3484_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3499_, size_t v_i_3500_, size_t v_stop_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3499_, v_i_3500_, v_stop_3501_, v___y_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3511_, lean_object* v_i_3512_, lean_object* v_stop_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
size_t v_i_boxed_3522_; size_t v_stop_boxed_3523_; lean_object* v_res_3524_; 
v_i_boxed_3522_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_stop_boxed_3523_ = lean_unbox_usize(v_stop_3513_);
lean_dec(v_stop_3513_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3511_, v_i_boxed_3522_, v_stop_boxed_3523_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_as_3511_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3525_, size_t v_i_3526_, size_t v_stop_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3525_, v_i_3526_, v_stop_3527_, v_b_3528_, v___y_3530_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3535_, lean_object* v_i_3536_, lean_object* v_stop_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
size_t v_i_boxed_3544_; size_t v_stop_boxed_3545_; lean_object* v_res_3546_; 
v_i_boxed_3544_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_stop_boxed_3545_ = lean_unbox_usize(v_stop_3537_);
lean_dec(v_stop_3537_);
v_res_3546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3535_, v_i_boxed_3544_, v_stop_boxed_3545_, v_b_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v_as_3535_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3547_, size_t v_i_3548_, size_t v_stop_3549_, lean_object* v_b_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3547_, v_i_3548_, v_stop_3549_, v_b_3550_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3560_, lean_object* v_i_3561_, lean_object* v_stop_3562_, lean_object* v_b_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
size_t v_i_boxed_3572_; size_t v_stop_boxed_3573_; lean_object* v_res_3574_; 
v_i_boxed_3572_ = lean_unbox_usize(v_i_3561_);
lean_dec(v_i_3561_);
v_stop_boxed_3573_ = lean_unbox_usize(v_stop_3562_);
lean_dec(v_stop_3562_);
v_res_3574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3560_, v_i_boxed_3572_, v_stop_boxed_3573_, v_b_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v_as_3560_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3575_, size_t v_i_3576_, size_t v_stop_3577_, lean_object* v_b_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3575_, v_i_3576_, v_stop_3577_, v_b_3578_, v___y_3583_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3588_, lean_object* v_i_3589_, lean_object* v_stop_3590_, lean_object* v_b_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
size_t v_i_boxed_3600_; size_t v_stop_boxed_3601_; lean_object* v_res_3602_; 
v_i_boxed_3600_ = lean_unbox_usize(v_i_3589_);
lean_dec(v_i_3589_);
v_stop_boxed_3601_ = lean_unbox_usize(v_stop_3590_);
lean_dec(v_stop_3590_);
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3588_, v_i_boxed_3600_, v_stop_boxed_3601_, v_b_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v_as_3588_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3603_, size_t v_i_3604_, size_t v_stop_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3603_, v_i_3604_, v_stop_3605_, v___y_3607_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3615_, lean_object* v_i_3616_, lean_object* v_stop_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_i_boxed_3626_; size_t v_stop_boxed_3627_; lean_object* v_res_3628_; 
v_i_boxed_3626_ = lean_unbox_usize(v_i_3616_);
lean_dec(v_i_3616_);
v_stop_boxed_3627_ = lean_unbox_usize(v_stop_3617_);
lean_dec(v_stop_3617_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3615_, v_i_boxed_3626_, v_stop_boxed_3627_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_as_3615_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3629_, size_t v_sz_3630_, size_t v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3629_, v_sz_3630_, v_i_3631_, v_b_3632_, v___y_3634_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3642_, lean_object* v_sz_3643_, lean_object* v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
size_t v_sz_boxed_3654_; size_t v_i_boxed_3655_; lean_object* v_res_3656_; 
v_sz_boxed_3654_ = lean_unbox_usize(v_sz_3643_);
lean_dec(v_sz_3643_);
v_i_boxed_3655_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_res_3656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3642_, v_sz_boxed_3654_, v_i_boxed_3655_, v_b_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_as_3642_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3657_, lean_object* v_x_3658_, size_t v_x_3659_, size_t v_x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3658_, v_x_3659_, v_x_3660_, v_x_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
size_t v_x_47683__boxed_3670_; size_t v_x_47684__boxed_3671_; lean_object* v_res_3672_; 
v_x_47683__boxed_3670_ = lean_unbox_usize(v_x_3666_);
lean_dec(v_x_3666_);
v_x_47684__boxed_3671_ = lean_unbox_usize(v_x_3667_);
lean_dec(v_x_3667_);
v_res_3672_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3664_, v_x_3665_, v_x_47683__boxed_3670_, v_x_47684__boxed_3671_, v_x_3668_, v_x_3669_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3673_, uint8_t v_t_3674_, lean_object* v_i_3675_, lean_object* v_as_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3673_, v_t_3674_, v_i_3675_, v_as_3676_, v___y_3678_, v___y_3681_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3686_, lean_object* v_t_3687_, lean_object* v_i_3688_, lean_object* v_as_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
uint8_t v_pu_boxed_3698_; uint8_t v_t_boxed_3699_; lean_object* v_res_3700_; 
v_pu_boxed_3698_ = lean_unbox(v_pu_3686_);
v_t_boxed_3699_ = lean_unbox(v_t_3687_);
v_res_3700_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3698_, v_t_boxed_3699_, v_i_3688_, v_as_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3701_, lean_object* v_n_3702_, lean_object* v_k_3703_, lean_object* v_v_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3702_, v_k_3703_, v_v_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3706_, size_t v_depth_3707_, lean_object* v_keys_3708_, lean_object* v_vals_3709_, lean_object* v_heq_3710_, lean_object* v_i_3711_, lean_object* v_entries_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3707_, v_keys_3708_, v_vals_3709_, v_i_3711_, v_entries_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3714_, lean_object* v_depth_3715_, lean_object* v_keys_3716_, lean_object* v_vals_3717_, lean_object* v_heq_3718_, lean_object* v_i_3719_, lean_object* v_entries_3720_){
_start:
{
size_t v_depth_boxed_3721_; lean_object* v_res_3722_; 
v_depth_boxed_3721_ = lean_unbox_usize(v_depth_3715_);
lean_dec(v_depth_3715_);
v_res_3722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3714_, v_depth_boxed_3721_, v_keys_3716_, v_vals_3717_, v_heq_3718_, v_i_3719_, v_entries_3720_);
lean_dec_ref(v_vals_3717_);
lean_dec_ref(v_keys_3716_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3723_, lean_object* v_x_3724_, lean_object* v_x_3725_, lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3724_, v_x_3725_, v_x_3726_, v_x_3727_);
return v___x_3728_;
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
