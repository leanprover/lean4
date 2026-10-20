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
uint8_t v___x_23072__boxed_818_; size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v___x_23072__boxed_818_ = lean_unbox(v___x_814_);
v_sz_boxed_819_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_820_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_23072__boxed_818_, v_sz_boxed_819_, v_i_boxed_820_, v_bs_817_);
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
size_t v_x_43480__boxed_1268_; size_t v_x_43481__boxed_1269_; lean_object* v_res_1270_; 
v_x_43480__boxed_1268_ = lean_unbox_usize(v_x_1264_);
lean_dec(v_x_1264_);
v_x_43481__boxed_1269_ = lean_unbox_usize(v_x_1265_);
lean_dec(v_x_1265_);
v_res_1270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1263_, v_x_43480__boxed_1268_, v_x_43481__boxed_1269_, v_x_1266_, v_x_1267_);
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
lean_object* v_a_1453_; uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_eq(v_i_1444_, v_stop_1445_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_array_uget_borrowed(v_as_1443_, v_i_1444_);
v___x_1460_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1459_);
v___x_1461_ = lean_array_get_size(v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_nat_dec_lt(v___x_1458_, v___x_1461_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v___x_1460_);
v_a_1453_ = v___x_1462_;
goto v___jp_1452_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1461_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1460_, v___x_1464_, v___x_1465_, v___x_1462_, v___y_1448_);
lean_dec_ref(v___x_1460_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_a_1453_ = v_a_1467_;
goto v___jp_1452_;
}
else
{
return v___x_1466_;
}
}
}
else
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1446_);
return v___x_1468_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1469_, lean_object* v_i_1470_, lean_object* v_stop_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
size_t v_i_boxed_1478_; size_t v_stop_boxed_1479_; lean_object* v_res_1480_; 
v_i_boxed_1478_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_stop_boxed_1479_ = lean_unbox_usize(v_stop_1471_);
lean_dec(v_stop_1471_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1469_, v_i_boxed_1478_, v_stop_boxed_1479_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1481_, size_t v_i_1482_, size_t v_stop_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_usize_dec_eq(v_i_1482_, v_stop_1483_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v_fvarId_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = lean_array_uget_borrowed(v_as_1481_, v_i_1482_);
v_fvarId_1488_ = lean_ctor_get(v___x_1487_, 0);
v___x_1489_ = 1;
v___x_1490_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1488_, v___y_1484_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1503_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1503_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1503_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_unbox(v_a_1491_);
lean_dec(v_a_1491_);
if (v___x_1495_ == 0)
{
size_t v___x_1496_; size_t v___x_1497_; 
lean_del_object(v___x_1493_);
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1482_, v___x_1496_);
v_i_1482_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_box(v___x_1489_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1499_);
v___x_1501_ = v___x_1493_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
return v___x_1490_;
}
}
else
{
uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = 0;
v___x_1505_ = lean_box(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1507_, lean_object* v_i_1508_, lean_object* v_stop_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
size_t v_i_boxed_1512_; size_t v_stop_boxed_1513_; lean_object* v_res_1514_; 
v_i_boxed_1512_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_stop_boxed_1513_ = lean_unbox_usize(v_stop_1509_);
lean_dec(v_stop_1509_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1507_, v_i_boxed_1512_, v_stop_boxed_1513_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v_as_1507_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1518_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1519_ = lean_unsigned_to_nat(9u);
v___x_1520_ = lean_unsigned_to_nat(650u);
v___x_1521_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1522_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1523_ = l_mkPanicMessageWithDecl(v___x_1522_, v___x_1521_, v___x_1520_, v___x_1519_, v___x_1518_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v_fvarId_1529_, lean_object* v_k_1530_, lean_object* v_args_1531_, uint8_t v___x_1532_, lean_object* v___x_1533_, lean_object* v_result_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_lower_1544_; lean_object* v_upper_1545_; uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_lt(v___x_1527_, v___x_1528_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
lean_dec(v___x_1533_);
lean_dec_ref(v_args_1531_);
lean_dec(v___x_1528_);
lean_dec(v___x_1527_);
v___x_1573_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1529_, v_result_1534_, v___y_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1573_, 1);
lean_inc_ref(v___y_1540_);
v___x_1574_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1530_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_k_1530_);
v_a_1575_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1573_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1573_);
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
else
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_le(v___x_1527_, v___x_1533_);
if (v___x_1583_ == 0)
{
lean_dec(v___x_1533_);
v_lower_1544_ = v___x_1527_;
v_upper_1545_ = v___x_1528_;
goto v___jp_1543_;
}
else
{
lean_dec(v___x_1527_);
v_lower_1544_ = v___x_1533_;
v_upper_1545_ = v___x_1528_;
goto v___jp_1543_;
}
}
v___jp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1546_ = l_Array_toSubarray___redArg(v_args_1531_, v_lower_1544_, v_upper_1545_);
v___x_1547_ = l_Subarray_copy___redArg(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_result_1534_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1550_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1532_, v___x_1548_, v___x_1549_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_fvarId_1552_; lean_object* v___x_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_fvarId_1552_ = lean_ctor_get(v_a_1551_, 0);
lean_inc(v_fvarId_1552_);
v___x_1553_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1529_, v_fvarId_1552_, v___y_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec_ref_known(v___x_1553_, 1);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_a_1551_);
lean_ctor_set(v___x_1554_, 1, v_k_1530_);
lean_inc_ref(v___y_1540_);
v___x_1555_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1554_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1555_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1551_);
lean_dec_ref(v_k_1530_);
v_a_1556_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1553_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1553_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_k_1530_);
lean_dec(v_fvarId_1529_);
v_a_1564_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1550_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1550_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_fvarId_1586_, lean_object* v_k_1587_, lean_object* v_args_1588_, lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v_result_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_43988__boxed_1600_; lean_object* v_res_1601_; 
v___x_43988__boxed_1600_ = lean_unbox(v___x_1589_);
v_res_1601_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1584_, v___x_1585_, v_fvarId_1586_, v_k_1587_, v_args_1588_, v___x_43988__boxed_1600_, v___x_1590_, v_result_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1602_, lean_object* v_k_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_fvarId_1612_; lean_object* v_value_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1951_; 
v_fvarId_1612_ = lean_ctor_get(v_letDecl_1602_, 0);
v_value_1613_ = lean_ctor_get(v_letDecl_1602_, 3);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_letDecl_1602_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1952_ = lean_ctor_get(v_letDecl_1602_, 2);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_letDecl_1602_, 1);
lean_dec(v_unused_1953_);
v___x_1615_ = v_letDecl_1602_;
v_isShared_1616_ = v_isSharedCheck_1951_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_value_1613_);
lean_inc(v_fvarId_1612_);
lean_dec(v_letDecl_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1951_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; 
lean_inc(v_value_1613_);
v___x_1617_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1613_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1942_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1942_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1942_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
if (lean_obj_tag(v_a_1618_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1937_; 
lean_del_object(v___x_1620_);
v_val_1622_ = lean_ctor_get(v_a_1618_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1624_ = v_a_1618_;
v_isShared_1625_ = v_isSharedCheck_1937_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v_a_1618_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1937_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_params_1626_; lean_object* v_value_1627_; lean_object* v_fType_1628_; lean_object* v_args_1629_; uint8_t v_recursive_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; 
v_params_1626_ = lean_ctor_get(v_val_1622_, 0);
v_value_1627_ = lean_ctor_get(v_val_1622_, 1);
v_fType_1628_ = lean_ctor_get(v_val_1622_, 2);
v_args_1629_ = lean_ctor_get(v_val_1622_, 3);
v_recursive_1630_ = lean_ctor_get_uint8(v_val_1622_, sizeof(void*)*4 + 2);
v___x_1631_ = lean_array_get_size(v_args_1629_);
v___x_1632_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1622_);
v___x_1633_ = lean_nat_dec_lt(v___x_1631_, v___x_1632_);
if (lean_obj_tag(v_value_1613_) == 3)
{
lean_object* v_declName_1917_; lean_object* v___x_1918_; 
v_declName_1917_ = lean_ctor_get(v_value_1613_, 0);
lean_inc_n(v_declName_1917_, 2);
lean_dec_ref_known(v_value_1613_, 3);
v___x_1918_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1630_, v_declName_1917_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_declName_1920_; lean_object* v_config_1921_; lean_object* v_inlineStack_1922_; lean_object* v_inlineStackOccs_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_declName_1920_ = lean_ctor_get(v_a_1604_, 0);
v_config_1921_ = lean_ctor_get(v_a_1604_, 1);
v_inlineStack_1922_ = lean_ctor_get(v_a_1604_, 2);
v_inlineStackOccs_1923_ = lean_ctor_get(v_a_1604_, 3);
lean_inc(v_inlineStack_1922_);
lean_inc(v_declName_1917_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_declName_1917_);
lean_ctor_set(v___x_1924_, 1, v_inlineStack_1922_);
lean_inc_ref(v_inlineStackOccs_1923_);
v___x_1925_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1923_, v_declName_1917_, v_a_1919_);
lean_inc_ref(v_config_1921_);
lean_inc(v_declName_1920_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 3, v___x_1925_);
lean_ctor_set(v___x_1615_, 2, v___x_1924_);
lean_ctor_set(v___x_1615_, 1, v_config_1921_);
lean_ctor_set(v___x_1615_, 0, v_declName_1920_);
v___x_1927_ = v___x_1615_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_declName_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_config_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1816_ = v___x_1927_;
v___y_1817_ = v_a_1605_;
v___y_1818_ = v_a_1606_;
v___y_1819_ = v_a_1607_;
v___y_1820_ = v_a_1608_;
v___y_1821_ = v_a_1609_;
v___y_1822_ = v_a_1610_;
goto v___jp_1815_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_declName_1917_);
lean_dec(v___x_1632_);
lean_del_object(v___x_1624_);
lean_dec(v_val_1622_);
lean_del_object(v___x_1615_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
v_a_1929_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1918_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1918_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_del_object(v___x_1615_);
lean_dec(v_value_1613_);
lean_inc_ref(v_a_1604_);
v___y_1816_ = v_a_1604_;
v___y_1817_ = v_a_1605_;
v___y_1818_ = v_a_1606_;
v___y_1819_ = v_a_1607_;
v___y_1820_ = v_a_1608_;
v___y_1821_ = v_a_1609_;
v___y_1822_ = v_a_1610_;
goto v___jp_1815_;
}
v___jp_1634_:
{
lean_object* v___x_1648_; 
lean_inc_ref(v___y_1646_);
v___x_1648_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1644_, v___y_1638_, v___y_1641_, v___y_1642_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1641_);
if (lean_obj_tag(v___x_1650_) == 0)
{
uint8_t v___x_1651_; 
lean_dec_ref_known(v___x_1650_, 1);
v___x_1651_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1649_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v___y_1636_);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___y_1637_);
lean_dec(v___y_1637_);
lean_inc_ref(v___x_1652_);
v___x_1653_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1635_, v___x_1652_);
v___x_1654_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1640_, v_fType_1628_, v___x_1653_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc_n(v_a_1655_, 2);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = l_Lean_Expr_headBeta(v_a_1655_);
v___x_1657_ = l_Lean_Expr_isForall(v___x_1656_);
lean_dec_ref(v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___x_1652_);
v___x_1658_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1640_, v_a_1655_, v___x_1633_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_fvarId_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_fvarId_1660_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1639_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc(v_fvarId_1660_);
v___x_1661_ = lean_apply_9(v___y_1643_, v_fvarId_1660_, v___y_1638_, v___y_1641_, v___y_1642_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___x_1663_);
v___x_1665_ = lean_array_push(v___x_1664_, v_a_1659_);
v___x_1666_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1667_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1640_, v___x_1665_, v_a_1662_, v___x_1666_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_n(v_a_1668_, 2);
lean_dec_ref_known(v___x_1667_, 1);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1669_, 0, v_a_1668_);
lean_closure_set(v___f_1669_, 1, v___x_1663_);
v___x_1670_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1640_, v_a_1649_, v___f_1669_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1682_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1682_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1682_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1668_);
lean_ctor_set(v___x_1675_, 1, v_a_1671_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1675_);
v___x_1677_ = v___x_1624_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1679_ = v___x_1673_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_a_1668_);
lean_del_object(v___x_1624_);
v_a_1683_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1670_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1670_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1649_);
lean_del_object(v___x_1624_);
v_a_1691_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1667_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1667_);
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
lean_dec(v_a_1659_);
lean_dec(v_a_1649_);
lean_del_object(v___x_1624_);
v_a_1699_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1661_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1661_);
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
lean_dec(v_a_1649_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_del_object(v___x_1624_);
v_a_1707_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1658_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1658_);
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
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v_a_1655_);
v___x_1715_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1716_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1652_, v_a_1649_, v___x_1715_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1717_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v_fvarId_1720_; lean_object* v___x_1721_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v_fvarId_1720_ = lean_ctor_get(v_a_1719_, 0);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1639_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1638_);
lean_inc(v_fvarId_1720_);
v___x_1721_ = lean_apply_9(v___y_1643_, v_fvarId_1720_, v___y_1638_, v___y_1641_, v___y_1642_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_, lean_box(0));
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_a_1719_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_mk_empty_array_with_capacity(v___x_1724_);
v___x_1726_ = lean_array_push(v___x_1725_, v___x_1723_);
v___x_1727_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1726_, v_a_1722_, v___y_1638_, v___y_1641_, v___y_1642_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___x_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1738_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1738_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1738_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_a_1728_);
v___x_1733_ = v___x_1624_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
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
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_del_object(v___x_1624_);
v_a_1739_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1727_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1727_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1719_);
lean_dec_ref(v___y_1638_);
lean_del_object(v___x_1624_);
v_a_1747_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1721_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1721_);
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
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_del_object(v___x_1624_);
v_a_1755_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1718_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1718_);
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
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_del_object(v___x_1624_);
v_a_1763_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1716_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1716_);
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
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___x_1652_);
lean_dec(v_a_1649_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_del_object(v___x_1624_);
v_a_1771_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1654_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1654_);
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
else
{
lean_object* v___x_1779_; 
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_fType_1628_);
v___x_1779_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1640_, v_a_1649_, v___y_1636_, v___y_1639_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_a_1780_);
v___x_1785_ = v___x_1624_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1785_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
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
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_del_object(v___x_1624_);
v_a_1791_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1779_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1779_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1649_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_fType_1628_);
lean_del_object(v___x_1624_);
v_a_1799_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1650_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1650_);
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
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_fType_1628_);
lean_del_object(v___x_1624_);
v_a_1807_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1648_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1648_);
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
v___jp_1815_:
{
if (v___x_1633_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_inc_ref_n(v_args_1629_, 2);
lean_inc_ref(v_fType_1628_);
lean_inc_ref(v_value_1627_);
lean_inc_ref(v_params_1626_);
lean_dec(v_val_1622_);
v___x_1823_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1632_);
v___x_1824_ = l_Array_toSubarray___redArg(v_args_1629_, v___x_1823_, v___x_1632_);
lean_inc_ref(v___x_1824_);
v___x_1825_ = l_Subarray_copy___redArg(v___x_1824_);
v___x_1826_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1626_, v_value_1627_, v___x_1825_, v___x_1633_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec_ref(v_params_1626_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___f_1830_; lean_object* v___f_1831_; uint8_t v___x_1832_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = 0;
v___x_1829_ = lean_box(v___x_1828_);
lean_inc_ref(v_k_1603_);
lean_inc(v_fvarId_1612_);
lean_inc(v___x_1632_);
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1830_, 0, v___x_1632_);
lean_closure_set(v___f_1830_, 1, v___x_1631_);
lean_closure_set(v___f_1830_, 2, v_fvarId_1612_);
lean_closure_set(v___f_1830_, 3, v_k_1603_);
lean_closure_set(v___f_1830_, 4, v_args_1629_);
lean_closure_set(v___f_1830_, 5, v___x_1829_);
lean_closure_set(v___f_1830_, 6, v___x_1823_);
lean_inc_ref(v___y_1818_);
lean_inc_ref(v___y_1816_);
lean_inc_ref(v___f_1830_);
lean_inc(v___y_1817_);
v___f_1831_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1831_, 0, v___y_1817_);
lean_closure_set(v___f_1831_, 1, v___f_1830_);
lean_closure_set(v___f_1831_, 2, v___y_1816_);
lean_closure_set(v___f_1831_, 3, v___y_1818_);
v___x_1832_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1603_, v_fvarId_1612_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
if (v___x_1832_ == 0)
{
lean_dec(v___x_1632_);
v___y_1635_ = v___x_1824_;
v___y_1636_ = v___f_1831_;
v___y_1637_ = v___x_1823_;
v___y_1638_ = v___y_1816_;
v___y_1639_ = v___y_1819_;
v___y_1640_ = v___x_1828_;
v___y_1641_ = v___y_1817_;
v___y_1642_ = v___y_1818_;
v___y_1643_ = v___f_1830_;
v___y_1644_ = v_a_1827_;
v___y_1645_ = v___y_1820_;
v___y_1646_ = v___y_1821_;
v___y_1647_ = v___y_1822_;
goto v___jp_1634_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_eq(v___x_1631_, v___x_1632_);
lean_dec(v___x_1632_);
if (v___x_1833_ == 0)
{
v___y_1635_ = v___x_1824_;
v___y_1636_ = v___f_1831_;
v___y_1637_ = v___x_1823_;
v___y_1638_ = v___y_1816_;
v___y_1639_ = v___y_1819_;
v___y_1640_ = v___x_1828_;
v___y_1641_ = v___y_1817_;
v___y_1642_ = v___y_1818_;
v___y_1643_ = v___f_1830_;
v___y_1644_ = v_a_1827_;
v___y_1645_ = v___y_1820_;
v___y_1646_ = v___y_1821_;
v___y_1647_ = v___y_1822_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1834_; 
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v_fType_1628_);
lean_del_object(v___x_1624_);
v___x_1834_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1817_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref_known(v___x_1834_, 1);
lean_inc_ref(v___y_1821_);
v___x_1835_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1827_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec_ref(v___y_1816_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
v_a_1845_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1835_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1835_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1827_);
lean_dec_ref(v___y_1816_);
v_a_1853_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1834_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1834_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___y_1816_);
lean_dec(v___x_1632_);
lean_dec_ref(v_args_1629_);
lean_dec_ref(v_fType_1628_);
lean_del_object(v___x_1624_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
v_a_1861_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1826_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1826_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v___x_1869_; 
lean_dec(v___x_1632_);
lean_del_object(v___x_1624_);
v___x_1869_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1622_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_fvarId_1871_; lean_object* v___x_1872_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_fvarId_1871_ = lean_ctor_get(v_a_1870_, 0);
lean_inc(v_fvarId_1871_);
v___x_1872_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1612_, v_fvarId_1871_, v___y_1817_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref_known(v___x_1872_, 1);
v___x_1873_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1817_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref_known(v___x_1873_, 1);
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1870_);
lean_ctor_set(v___x_1874_, 1, v_k_1603_);
lean_inc_ref(v___y_1821_);
v___x_1875_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1874_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec_ref(v___y_1816_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1884_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1884_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1880_);
v___x_1882_ = v___x_1878_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1875_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1875_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1870_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_k_1603_);
v_a_1893_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1873_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1873_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1870_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_k_1603_);
v_a_1901_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1872_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1872_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___y_1816_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
v_a_1909_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1869_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1869_);
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
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v_a_1618_);
lean_del_object(v___x_1615_);
lean_dec(v_value_1613_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
v___x_1938_ = lean_box(0);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1938_);
v___x_1940_ = v___x_1620_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
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
lean_del_object(v___x_1615_);
lean_dec(v_value_1613_);
lean_dec(v_fvarId_1612_);
lean_dec_ref(v_k_1603_);
v_a_1943_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1617_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1617_);
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
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_typeName_1967_; lean_object* v_discr_1968_; uint8_t v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_subst_1973_; lean_object* v___x_1974_; 
v_typeName_1967_ = lean_ctor_get(v_cases_1955_, 0);
v_discr_1968_ = lean_ctor_get(v_cases_1955_, 2);
v___x_1969_ = 0;
v___x_1970_ = 0;
v___x_1971_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_1972_ = lean_st_ref_get(v_a_1957_);
v_subst_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc_ref(v_subst_1973_);
lean_dec(v___x_1972_);
lean_inc(v_discr_1968_);
v___x_1974_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1973_, v_discr_1968_, v___x_1970_);
lean_dec_ref(v_subst_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_fvarId_1975_; lean_object* v___x_1976_; 
v_fvarId_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_fvarId_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1975_, v_a_1958_, v_a_1960_, v_a_1962_);
lean_dec(v_fvarId_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2205_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_2205_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2205_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
if (lean_obj_tag(v_a_1977_) == 1)
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2200_; 
v_val_1981_ = lean_ctor_get(v_a_1977_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_1983_ = v_a_1977_;
v_isShared_1984_ = v_isSharedCheck_2200_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v_a_1977_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2200_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v_env_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1985_ = lean_st_ref_get(v_a_1962_);
v_env_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_ref(v_env_1986_);
lean_dec(v___x_1985_);
v___x_1987_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1981_);
lean_inc(v___x_1987_);
v___x_1988_ = l_Lean_Environment_find_x3f(v_env_1986_, v___x_1987_, v___x_1970_);
if (lean_obj_tag(v___x_1988_) == 1)
{
lean_object* v_val_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2199_; 
v_val_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2199_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_val_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2199_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
if (lean_obj_tag(v_val_1989_) == 6)
{
lean_object* v_val_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2198_; 
v_val_1993_ = lean_ctor_get(v_val_1989_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_val_1989_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_1995_ = v_val_1989_;
v_isShared_1996_ = v_isSharedCheck_2198_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_val_1993_);
lean_dec(v_val_1989_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2198_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_induct_1997_; uint8_t v___x_1998_; 
v_induct_1997_ = lean_ctor_get(v_val_1993_, 1);
lean_inc(v_induct_1997_);
lean_dec_ref(v_val_1993_);
v___x_1998_ = lean_name_eq(v_typeName_1967_, v_induct_1997_);
lean_dec(v_induct_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_del_object(v___x_1995_);
lean_del_object(v___x_1991_);
lean_dec(v___x_1987_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
lean_dec_ref(v_cases_1955_);
v___x_1999_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1999_);
v___x_2001_ = v___x_1979_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v___x_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_1979_);
v___x_2003_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1969_, v_cases_1955_, v___x_1987_);
v_fst_2004_ = lean_ctor_get(v___x_2003_, 0);
v_snd_2005_ = lean_ctor_get(v___x_2003_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2007_ = v___x_2003_;
v_isShared_2008_ = v_isSharedCheck_2197_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v___x_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2197_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 4);
lean_ctor_set(v___x_1995_, 0, v_snd_2005_);
v___x_2010_ = v___x_1995_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_snd_2005_);
v___x_2010_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1969_, v___x_2010_, v_a_1960_);
lean_dec_ref(v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref_known(v___x_2011_, 1);
v___x_2012_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1957_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref_known(v___x_2012_, 1);
if (lean_obj_tag(v_fst_2004_) == 0)
{
if (lean_obj_tag(v_val_1981_) == 0)
{
lean_object* v_params_2013_; lean_object* v_code_2014_; lean_object* v_val_2015_; lean_object* v_args_2016_; lean_object* v_lower_2018_; lean_object* v_upper_2019_; lean_object* v_numParams_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
lean_del_object(v___x_2007_);
lean_del_object(v___x_1983_);
v_params_2013_ = lean_ctor_get(v_fst_2004_, 1);
lean_inc_ref(v_params_2013_);
v_code_2014_ = lean_ctor_get(v_fst_2004_, 2);
lean_inc_ref(v_code_2014_);
lean_dec_ref_known(v_fst_2004_, 3);
v_val_2015_ = lean_ctor_get(v_val_1981_, 0);
lean_inc_ref(v_val_2015_);
v_args_2016_ = lean_ctor_get(v_val_1981_, 1);
lean_inc_ref(v_args_2016_);
lean_dec_ref_known(v_val_1981_, 2);
v_numParams_2062_ = lean_ctor_get(v_val_2015_, 3);
lean_inc(v_numParams_2062_);
lean_dec_ref(v_val_2015_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_array_get_size(v_args_2016_);
v___x_2065_ = lean_nat_dec_le(v_numParams_2062_, v___x_2063_);
if (v___x_2065_ == 0)
{
v_lower_2018_ = v_numParams_2062_;
v_upper_2019_ = v___x_2064_;
goto v___jp_2017_;
}
else
{
lean_dec(v_numParams_2062_);
v_lower_2018_ = v___x_2063_;
v_upper_2019_ = v___x_2064_;
goto v___jp_2017_;
}
v___jp_2017_:
{
lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2020_ = l_Array_toSubarray___redArg(v_args_2016_, v_lower_2018_, v_upper_2019_);
v_sz_2021_ = lean_array_size(v_params_2013_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2013_, v_sz_2021_, v___x_2022_, v___x_2020_, v_a_1957_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2024_; 
lean_dec_ref_known(v___x_2023_, 1);
lean_inc_ref(v_a_1961_);
v___x_2024_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2014_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1969_, v_params_2013_, v_a_1960_);
lean_dec_ref(v_params_2013_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2036_; 
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2026_, 0);
lean_dec(v_unused_2037_);
v___x_2028_ = v___x_2026_;
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2026_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_a_2025_);
v___x_2031_ = v___x_1991_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2025_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_2025_);
lean_del_object(v___x_1991_);
v_a_2038_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2026_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2026_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
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
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v_params_2013_);
lean_del_object(v___x_1991_);
v_a_2046_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2024_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2024_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v_code_2014_);
lean_dec_ref(v_params_2013_);
lean_del_object(v___x_1991_);
v_a_2054_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2023_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2023_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
else
{
lean_object* v_params_2066_; lean_object* v_code_2067_; lean_object* v_n_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2158_; 
v_params_2066_ = lean_ctor_get(v_fst_2004_, 1);
lean_inc_ref(v_params_2066_);
v_code_2067_ = lean_ctor_get(v_fst_2004_, 2);
lean_inc_ref(v_code_2067_);
lean_dec_ref_known(v_fst_2004_, 3);
v_n_2068_ = lean_ctor_get(v_val_1981_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_val_1981_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2070_ = v_val_1981_;
v_isShared_2071_ = v_isSharedCheck_2158_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_n_2068_);
lean_dec(v_val_1981_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2158_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_zero_2072_; uint8_t v_isZero_2073_; 
v_zero_2072_ = lean_unsigned_to_nat(0u);
v_isZero_2073_ = lean_nat_dec_eq(v_n_2068_, v_zero_2072_);
if (v_isZero_2073_ == 1)
{
lean_object* v___x_2074_; 
lean_del_object(v___x_2070_);
lean_dec(v_n_2068_);
lean_dec_ref(v_params_2066_);
lean_del_object(v___x_2007_);
lean_del_object(v___x_1983_);
lean_inc_ref(v_a_1961_);
v___x_2074_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2067_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2085_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_a_2075_);
v___x_2080_ = v___x_1991_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2082_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2080_);
v___x_2082_ = v___x_2077_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
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
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_del_object(v___x_1991_);
v_a_2086_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2074_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2074_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_one_2094_; lean_object* v_n_2095_; lean_object* v___x_2097_; 
v_one_2094_ = lean_unsigned_to_nat(1u);
v_n_2095_ = lean_nat_sub(v_n_2068_, v_one_2094_);
lean_dec(v_n_2068_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 0);
lean_ctor_set(v___x_2070_, 0, v_n_2095_);
v___x_2097_ = v___x_2070_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_n_2095_);
v___x_2097_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 0);
lean_ctor_set(v___x_1983_, 0, v___x_2097_);
v___x_2099_ = v___x_1983_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2101_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1969_, v___x_2099_, v___x_2100_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v_fvarId_2104_; lean_object* v_fvarId_2105_; lean_object* v___x_2106_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_array_get_borrowed(v___x_1971_, v_params_2066_, v_zero_2072_);
v_fvarId_2104_ = lean_ctor_get(v___x_2103_, 0);
v_fvarId_2105_ = lean_ctor_get(v_a_2102_, 0);
lean_inc(v_fvarId_2105_);
lean_inc(v_fvarId_2104_);
v___x_2106_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2104_, v_fvarId_2105_, v_a_1957_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2107_; 
lean_dec_ref_known(v___x_2106_, 1);
lean_inc_ref(v_a_1961_);
v___x_2107_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2067_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1969_, v_params_2066_, v_a_1960_);
lean_dec_ref(v_params_2066_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2122_; 
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2123_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v_a_2108_);
lean_ctor_set(v___x_2007_, 0, v_a_2102_);
v___x_2114_ = v___x_2007_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2102_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_a_2108_);
v___x_2114_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2114_);
v___x_2116_ = v___x_1991_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2116_);
v___x_2118_ = v___x_2111_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_a_2108_);
lean_dec(v_a_2102_);
lean_del_object(v___x_2007_);
lean_del_object(v___x_1991_);
v_a_2124_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2109_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2109_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_a_2102_);
lean_dec_ref(v_params_2066_);
lean_del_object(v___x_2007_);
lean_del_object(v___x_1991_);
v_a_2132_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2107_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2107_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2102_);
lean_dec_ref(v_code_2067_);
lean_dec_ref(v_params_2066_);
lean_del_object(v___x_2007_);
lean_del_object(v___x_1991_);
v_a_2140_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2106_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2106_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_code_2067_);
lean_dec_ref(v_params_2066_);
lean_del_object(v___x_2007_);
lean_del_object(v___x_1991_);
v_a_2148_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2101_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2101_);
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
}
}
}
}
}
else
{
lean_object* v_code_2159_; lean_object* v___x_2160_; 
lean_del_object(v___x_2007_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
v_code_2159_ = lean_ctor_get(v_fst_2004_, 0);
lean_inc_ref(v_code_2159_);
lean_dec_ref_known(v_fst_2004_, 1);
lean_inc_ref(v_a_1961_);
v___x_2160_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2159_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2171_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2171_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2171_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_a_2161_);
v___x_2166_ = v___x_1991_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
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
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_1991_);
v_a_2172_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2160_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2160_);
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
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2007_);
lean_dec(v_fst_2004_);
lean_del_object(v___x_1991_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
v_a_2180_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2012_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2012_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_del_object(v___x_2007_);
lean_dec(v_fst_2004_);
lean_del_object(v___x_1991_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
v_a_2188_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2011_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2011_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
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
lean_del_object(v___x_1991_);
lean_dec(v_val_1989_);
lean_dec(v___x_1987_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
lean_del_object(v___x_1979_);
lean_dec_ref(v_cases_1955_);
goto v___jp_1964_;
}
}
}
else
{
lean_dec(v___x_1988_);
lean_dec(v___x_1987_);
lean_del_object(v___x_1983_);
lean_dec(v_val_1981_);
lean_del_object(v___x_1979_);
lean_dec_ref(v_cases_1955_);
goto v___jp_1964_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_dec(v_a_1977_);
lean_dec_ref(v_cases_1955_);
v___x_2201_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2201_);
v___x_2203_ = v___x_1979_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
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
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_cases_1955_);
v_a_2206_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_1976_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_1976_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
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
lean_object* v___x_2214_; 
lean_dec_ref(v_cases_1955_);
v___x_2214_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1969_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_a_2215_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2219_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
v_a_2224_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2214_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2214_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
v___jp_1964_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2232_, lean_object* v_i_2233_, lean_object* v_as_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_array_get_size(v_as_2234_);
v___x_2244_ = lean_nat_dec_lt(v_i_2233_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_as_2234_);
return v___x_2245_;
}
else
{
lean_object* v_a_2246_; lean_object* v_a_2248_; 
v_a_2246_ = lean_array_fget_borrowed(v_as_2234_, v_i_2233_);
if (lean_obj_tag(v_a_2246_) == 0)
{
lean_object* v_ctorName_2259_; lean_object* v_params_2260_; lean_object* v_code_2261_; uint8_t v___x_2284_; uint8_t v_a_2286_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v_ctorName_2259_ = lean_ctor_get(v_a_2246_, 0);
v_params_2260_ = lean_ctor_get(v_a_2246_, 1);
v_code_2261_ = lean_ctor_get(v_a_2246_, 2);
v___x_2284_ = 0;
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_array_get_size(v_params_2260_);
v___x_2319_ = lean_nat_dec_lt(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
v_a_2286_ = v___x_2319_;
goto v___jp_2285_;
}
else
{
if (v___x_2319_ == 0)
{
v_a_2286_ = v___x_2319_;
goto v___jp_2285_;
}
else
{
size_t v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((size_t)0ULL);
v___x_2321_ = lean_usize_of_nat(v___x_2318_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2260_, v___x_2320_, v___x_2321_, v___y_2241_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; uint8_t v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
v_a_2286_ = v___x_2324_;
goto v___jp_2285_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v_a_2325_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2322_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2322_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
v___jp_2262_:
{
lean_object* v___x_2263_; 
lean_inc_ref(v_params_2260_);
lean_inc(v_ctorName_2259_);
lean_inc(v_fvarId_2232_);
v___x_2263_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2232_, v_ctorName_2259_, v_params_2260_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2263_, 1);
lean_inc_ref(v___y_2240_);
lean_inc_ref(v_code_2261_);
v___x_2265_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2261_, v___y_2235_, v___y_2236_, v_a_2264_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v_a_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
lean_inc_ref(v_a_2246_);
v___x_2267_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2246_, v_a_2266_);
v_a_2248_ = v___x_2267_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v_a_2268_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2265_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2265_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v_a_2276_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2263_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2263_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
v___jp_2285_:
{
if (lean_obj_tag(v_code_2261_) == 6)
{
goto v___jp_2262_;
}
else
{
if (v_a_2286_ == 0)
{
goto v___jp_2262_;
}
else
{
lean_object* v___x_2287_; 
lean_inc_ref(v_code_2261_);
v___x_2287_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2284_, v_code_2261_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2284_, v_code_2261_, v___y_2239_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref_known(v___x_2289_, 1);
v___x_2290_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2236_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref_known(v___x_2290_, 1);
v___x_2291_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_a_2288_);
lean_inc_ref(v_a_2246_);
v___x_2292_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2246_, v___x_2291_);
v_a_2248_ = v___x_2292_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_2288_);
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
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
lean_dec(v_a_2288_);
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v_a_2301_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2289_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2289_);
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
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
v_a_2309_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2287_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2287_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2333_; lean_object* v___x_2334_; 
v_code_2333_ = lean_ctor_get(v_a_2246_, 0);
lean_inc_ref(v___y_2240_);
lean_inc_ref(v_code_2333_);
v___x_2334_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2333_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
lean_inc_ref(v_a_2246_);
v___x_2336_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2246_, v_a_2335_);
v_a_2248_ = v___x_2336_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec(v_fvarId_2232_);
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
v___jp_2247_:
{
size_t v___x_2249_; size_t v___x_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_ptr_addr(v_a_2246_);
v___x_2250_ = lean_ptr_addr(v_a_2248_);
v___x_2251_ = lean_usize_dec_eq(v___x_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v_i_2233_, v___x_2252_);
v___x_2254_ = lean_array_fset(v_as_2234_, v_i_2233_, v_a_2248_);
lean_dec(v_i_2233_);
v_i_2233_ = v___x_2253_;
v_as_2234_ = v___x_2254_;
goto _start;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec_ref(v_a_2248_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v_i_2233_, v___x_2256_);
lean_dec(v_i_2233_);
v_i_2233_ = v___x_2257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___y_2356_; lean_object* v___y_2357_; uint8_t v___y_2420_; lean_object* v___y_2421_; lean_object* v_decl_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; uint8_t v___y_2471_; lean_object* v___y_2472_; lean_object* v_decl_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v_decl_2492_; lean_object* v_k_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; uint8_t v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v_decl_2773_; lean_object* v_fvarId_2774_; lean_object* v_type_2775_; lean_object* v_value_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v_toCold_3241_; lean_object* v_currRecDepth_3242_; lean_object* v_ref_3243_; uint16_t v_optionFlags_3244_; uint8_t v_suppressElabErrors_3245_; uint8_t v_isRecordingDeps_3246_; lean_object* v_maxRecDepth_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v_toCold_3241_ = lean_ctor_get(v_a_2352_, 0);
v_currRecDepth_3242_ = lean_ctor_get(v_a_2352_, 1);
v_ref_3243_ = lean_ctor_get(v_a_2352_, 2);
v_optionFlags_3244_ = lean_ctor_get_uint16(v_a_2352_, sizeof(void*)*3);
v_suppressElabErrors_3245_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3246_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*3 + 3);
v_maxRecDepth_3276_ = lean_ctor_get(v_toCold_3241_, 3);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = lean_nat_dec_eq(v_maxRecDepth_3276_, v___x_3277_);
if (v___x_3278_ == 0)
{
uint8_t v___x_3279_; 
v___x_3279_ = lean_nat_dec_eq(v_currRecDepth_3242_, v_maxRecDepth_3276_);
if (v___x_3279_ == 0)
{
lean_inc(v_ref_3243_);
lean_inc(v_currRecDepth_3242_);
lean_inc_ref(v_toCold_3241_);
lean_dec_ref(v_a_2352_);
goto v___jp_3247_;
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref(v_code_2346_);
v___x_3280_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec_ref(v_a_2352_);
return v___x_3280_;
}
}
else
{
lean_inc(v_ref_3243_);
lean_inc(v_currRecDepth_3242_);
lean_inc_ref(v_toCold_3241_);
lean_dec_ref(v_a_2352_);
goto v___jp_3247_;
}
v___jp_2355_:
{
switch(lean_obj_tag(v_code_2346_))
{
case 1:
{
lean_object* v_decl_2358_; lean_object* v_k_2359_; size_t v___x_2360_; size_t v___x_2361_; uint8_t v___x_2362_; 
v_decl_2358_ = lean_ctor_get(v_code_2346_, 0);
v_k_2359_ = lean_ctor_get(v_code_2346_, 1);
v___x_2360_ = lean_ptr_addr(v_k_2359_);
v___x_2361_ = lean_ptr_addr(v___y_2356_);
v___x_2362_ = lean_usize_dec_eq(v___x_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; lean_object* v_unused_2372_; 
v_unused_2371_ = lean_ctor_get(v_code_2346_, 1);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_2372_);
v___x_2364_ = v_code_2346_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v_code_2346_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___y_2356_);
lean_ctor_set(v___x_2364_, 0, v___y_2357_);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___y_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___y_2356_);
v___x_2367_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
else
{
size_t v___x_2373_; size_t v___x_2374_; uint8_t v___x_2375_; 
v___x_2373_ = lean_ptr_addr(v_decl_2358_);
v___x_2374_ = lean_ptr_addr(v___y_2357_);
v___x_2375_ = lean_usize_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2383_; 
v_isSharedCheck_2383_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; lean_object* v_unused_2385_; 
v_unused_2384_ = lean_ctor_get(v_code_2346_, 1);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_2385_);
v___x_2377_ = v_code_2346_;
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v_code_2346_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 1, v___y_2356_);
lean_ctor_set(v___x_2377_, 0, v___y_2357_);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___y_2357_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___y_2356_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
else
{
lean_object* v___x_2386_; 
lean_dec_ref(v___y_2357_);
lean_dec_ref(v___y_2356_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_code_2346_);
return v___x_2386_;
}
}
}
case 2:
{
lean_object* v_decl_2387_; lean_object* v_k_2388_; size_t v___x_2389_; size_t v___x_2390_; uint8_t v___x_2391_; 
v_decl_2387_ = lean_ctor_get(v_code_2346_, 0);
v_k_2388_ = lean_ctor_get(v_code_2346_, 1);
v___x_2389_ = lean_ptr_addr(v_k_2388_);
v___x_2390_ = lean_ptr_addr(v___y_2356_);
v___x_2391_ = lean_usize_dec_eq(v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_isSharedCheck_2399_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2400_ = lean_ctor_get(v_code_2346_, 1);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_2401_);
v___x_2393_ = v_code_2346_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v_code_2346_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___y_2356_);
lean_ctor_set(v___x_2393_, 0, v___y_2357_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___y_2357_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___y_2356_);
v___x_2396_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
}
else
{
size_t v___x_2402_; size_t v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_ptr_addr(v_decl_2387_);
v___x_2403_ = lean_ptr_addr(v___y_2357_);
v___x_2404_ = lean_usize_dec_eq(v___x_2402_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
v_isSharedCheck_2412_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; lean_object* v_unused_2414_; 
v_unused_2413_ = lean_ctor_get(v_code_2346_, 1);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_2414_);
v___x_2406_ = v_code_2346_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v_code_2346_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 1, v___y_2356_);
lean_ctor_set(v___x_2406_, 0, v___y_2357_);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___y_2357_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___y_2356_);
v___x_2409_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
}
else
{
lean_object* v___x_2415_; 
lean_dec_ref(v___y_2357_);
lean_dec_ref(v___y_2356_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_code_2346_);
return v___x_2415_;
}
}
}
default: 
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v_code_2346_);
v___x_2416_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2417_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
v___jp_2419_:
{
lean_object* v___x_2430_; 
lean_inc_ref(v___y_2428_);
v___x_2430_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2421_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v_fvarId_2432_; lean_object* v___x_2433_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_fvarId_2432_ = lean_ctor_get(v_decl_2422_, 0);
v___x_2433_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2432_, v___y_2424_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; uint8_t v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2435_ = lean_unbox(v_a_2434_);
lean_dec(v_a_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_code_2346_);
v___x_2436_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2422_, v___y_2424_, v___y_2427_);
lean_dec_ref(v_decl_2422_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2444_);
v___x_2438_ = v___x_2436_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v_a_2431_);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2431_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_a_2431_);
v_a_2445_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2436_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2436_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
if (v___y_2420_ == 0)
{
lean_dec_ref(v___y_2428_);
v___y_2356_ = v_a_2431_;
v___y_2357_ = v_decl_2422_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2453_; 
lean_inc_ref(v_decl_2422_);
v___x_2453_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec_ref(v___y_2428_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_dec_ref_known(v___x_2453_, 1);
v___y_2356_ = v_a_2431_;
v___y_2357_ = v_decl_2422_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2431_);
lean_dec_ref(v_decl_2422_);
lean_dec_ref(v_code_2346_);
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2431_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_decl_2422_);
lean_dec_ref(v_code_2346_);
v_a_2462_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2433_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2433_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_decl_2422_);
lean_dec_ref(v_code_2346_);
return v___x_2430_;
}
}
v___jp_2470_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___y_2420_ = v___y_2471_;
v___y_2421_ = v___y_2472_;
v_decl_2422_ = v_a_2482_;
v___y_2423_ = v___y_2474_;
v___y_2424_ = v___y_2475_;
v___y_2425_ = v___y_2476_;
v___y_2426_ = v___y_2477_;
v___y_2427_ = v___y_2478_;
v___y_2428_ = v___y_2479_;
v___y_2429_ = v___y_2480_;
goto v___jp_2419_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v_code_2346_);
v_a_2483_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2481_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
v___jp_2491_:
{
lean_object* v_fvarId_2501_; lean_object* v_params_2502_; lean_object* v_type_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; 
v_fvarId_2501_ = lean_ctor_get(v_decl_2492_, 0);
v_params_2502_ = lean_ctor_get(v_decl_2492_, 2);
v_type_2503_ = lean_ctor_get(v_decl_2492_, 3);
v___x_2504_ = 0;
v___x_2505_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2501_, v___y_2495_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; uint8_t v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_unbox(v_a_2506_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2346_);
if (v___x_2508_ == 0)
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
v___y_2471_ = v___x_2509_;
v___y_2472_ = v_k_2493_;
v_decl_2473_ = v_decl_2492_;
v___y_2474_ = v___y_2494_;
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2498_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
goto v___jp_2470_;
}
else
{
uint8_t v___x_2510_; 
lean_inc_ref(v_type_2503_);
v___x_2510_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2503_, v_params_2502_);
if (v___x_2510_ == 0)
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
v___y_2471_ = v___x_2511_;
v___y_2472_ = v_k_2493_;
v_decl_2473_ = v_decl_2492_;
v___y_2474_ = v___y_2494_;
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2498_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
goto v___jp_2470_;
}
else
{
lean_object* v___x_2512_; lean_object* v_subst_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = lean_st_ref_get(v___y_2495_);
v_subst_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_subst_2513_);
lean_dec(v___x_2512_);
v___x_2514_ = lean_unbox(v_a_2506_);
v___x_2515_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2504_, v___x_2514_, v_decl_2492_, v_subst_2513_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec_ref(v_subst_2513_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2516_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v___x_2519_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2495_);
if (lean_obj_tag(v___x_2519_) == 0)
{
uint8_t v___x_2520_; 
lean_dec_ref_known(v___x_2519_, 1);
v___x_2520_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
v___y_2471_ = v___x_2520_;
v___y_2472_ = v_k_2493_;
v_decl_2473_ = v_a_2518_;
v___y_2474_ = v___y_2494_;
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2498_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
goto v___jp_2470_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_a_2518_);
lean_dec(v_a_2506_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_k_2493_);
lean_dec_ref(v_code_2346_);
v_a_2521_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2519_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2519_);
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
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_a_2506_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_k_2493_);
lean_dec_ref(v_code_2346_);
v_a_2529_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2517_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2517_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2506_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_k_2493_);
lean_dec_ref(v_code_2346_);
v_a_2537_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2515_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2515_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
else
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v_subst_2547_; lean_object* v___x_2548_; 
v___x_2545_ = 0;
v___x_2546_ = lean_st_ref_get(v___y_2495_);
v_subst_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref(v_subst_2547_);
lean_dec(v___x_2546_);
v___x_2548_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2504_, v___x_2545_, v_decl_2492_, v_subst_2547_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec_ref(v_subst_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
v___y_2420_ = v___x_2550_;
v___y_2421_ = v_k_2493_;
v_decl_2422_ = v_a_2549_;
v___y_2423_ = v___y_2494_;
v___y_2424_ = v___y_2495_;
v___y_2425_ = v___y_2496_;
v___y_2426_ = v___y_2497_;
v___y_2427_ = v___y_2498_;
v___y_2428_ = v___y_2499_;
v___y_2429_ = v___y_2500_;
goto v___jp_2419_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2506_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_k_2493_);
lean_dec_ref(v_code_2346_);
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
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_k_2493_);
lean_dec_ref(v_decl_2492_);
lean_dec_ref(v_code_2346_);
v_a_2559_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2505_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2505_);
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
lean_object* v___x_2578_; 
lean_inc_ref(v___y_2574_);
v___x_2578_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2574_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
if (lean_obj_tag(v_a_2579_) == 1)
{
lean_object* v_val_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_val_2580_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_a_2579_, 1);
v___x_2581_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2570_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; 
lean_dec_ref_known(v___x_2581_, 1);
lean_inc_ref(v___y_2576_);
v___x_2582_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2572_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2580_, v_a_2583_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
lean_dec_ref(v___y_2576_);
lean_dec(v_val_2580_);
return v___x_2584_;
}
else
{
lean_dec(v_val_2580_);
lean_dec_ref(v___y_2576_);
return v___x_2582_;
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_val_2580_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2572_);
v_a_2585_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2581_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2581_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v___x_2593_; 
lean_dec(v_a_2579_);
lean_inc_ref(v___y_2574_);
v___x_2593_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2574_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
if (lean_obj_tag(v_a_2594_) == 1)
{
lean_object* v_val_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_val_2595_ = lean_ctor_get(v_a_2594_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v_a_2594_, 1);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_val_2595_);
lean_ctor_set(v___x_2596_, 1, v___y_2572_);
v_code_2346_ = v___x_2596_;
v_a_2347_ = v___y_2569_;
v_a_2348_ = v___y_2570_;
v_a_2349_ = v___y_2575_;
v_a_2350_ = v___y_2577_;
v_a_2351_ = v___y_2571_;
v_a_2352_ = v___y_2576_;
v_a_2353_ = v___y_2573_;
goto _start;
}
else
{
lean_object* v_fvarId_2598_; lean_object* v_value_2599_; lean_object* v___x_2600_; 
lean_dec(v_a_2594_);
v_fvarId_2598_ = lean_ctor_get(v___y_2574_, 0);
v_value_2599_ = lean_ctor_get(v___y_2574_, 3);
v___x_2600_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
if (lean_obj_tag(v_a_2601_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2603_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_val_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v_a_2601_, 1);
lean_inc(v_fvarId_2598_);
v___x_2603_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2598_, v_val_2602_, v___y_2570_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref_known(v___x_2603_, 1);
v___x_2604_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2574_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2574_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec_ref_known(v___x_2604_, 1);
v_code_2346_ = v___y_2572_;
v_a_2347_ = v___y_2569_;
v_a_2348_ = v___y_2570_;
v_a_2349_ = v___y_2575_;
v_a_2350_ = v___y_2577_;
v_a_2351_ = v___y_2571_;
v_a_2352_ = v___y_2576_;
v_a_2353_ = v___y_2573_;
goto _start;
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2572_);
v_a_2606_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2604_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2604_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
v_a_2614_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2603_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2603_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v___x_2622_; 
lean_dec(v_a_2601_);
lean_inc_ref(v___y_2572_);
lean_inc_ref(v___y_2574_);
v___x_2622_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2574_, v___y_2572_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
if (lean_obj_tag(v_a_2623_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_val_2624_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_val_2624_);
lean_dec_ref_known(v_a_2623_, 1);
v___x_2625_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2574_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2574_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2625_, 0);
lean_dec(v_unused_2633_);
v___x_2627_ = v___x_2625_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v___x_2625_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_val_2624_);
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_val_2624_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_val_2624_);
v_a_2634_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2625_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2625_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_a_2623_);
lean_inc(v_value_2599_);
v___x_2642_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2599_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
if (lean_obj_tag(v_a_2643_) == 1)
{
lean_object* v_val_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2647_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_val_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_val_2644_);
lean_dec_ref_known(v_a_2643_, 1);
v_fst_2645_ = lean_ctor_get(v_val_2644_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v_val_2644_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_val_2644_);
lean_inc(v_fvarId_2598_);
v___x_2647_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2598_, v_snd_2646_, v___y_2570_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2647_, 1);
v___x_2648_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2574_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2574_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2648_, 1);
lean_inc_ref(v___y_2576_);
v___x_2649_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2572_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2645_, v_a_2650_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
lean_dec_ref(v___y_2576_);
lean_dec(v_fst_2645_);
return v___x_2651_;
}
else
{
lean_dec(v_fst_2645_);
lean_dec_ref(v___y_2576_);
return v___x_2649_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_fst_2645_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2572_);
v_a_2652_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2648_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2648_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_fst_2645_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
v_a_2660_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2647_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2647_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v___x_2668_; 
lean_dec(v_a_2643_);
lean_inc_ref(v___y_2576_);
lean_inc_ref(v___y_2572_);
v___x_2668_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2572_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2598_, v___y_2570_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v___x_2673_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2574_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2574_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2673_, 0);
lean_dec(v_unused_2681_);
v___x_2675_ = v___x_2673_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v___x_2673_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v_a_2669_);
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2669_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2669_);
v_a_2682_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2673_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2673_);
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
else
{
lean_object* v___x_2690_; 
lean_inc_ref(v___y_2574_);
v___x_2690_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2574_, v___y_2569_, v___y_2570_, v___y_2575_, v___y_2577_, v___y_2571_, v___y_2576_, v___y_2573_);
lean_dec_ref(v___y_2576_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2711_; 
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v___x_2690_, 0);
lean_dec(v_unused_2712_);
v___x_2692_ = v___x_2690_;
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v___x_2690_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2711_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
size_t v___x_2694_; size_t v___x_2695_; uint8_t v___x_2696_; 
v___x_2694_ = lean_ptr_addr(v___y_2572_);
lean_dec_ref(v___y_2572_);
v___x_2695_ = lean_ptr_addr(v_a_2669_);
v___x_2696_ = lean_usize_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2574_);
lean_ctor_set(v___x_2697_, 1, v_a_2669_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2697_);
v___x_2699_ = v___x_2692_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
else
{
size_t v___x_2701_; size_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_ptr_addr(v___y_2568_);
lean_dec_ref(v___y_2568_);
v___x_2702_ = lean_ptr_addr(v___y_2574_);
v___x_2703_ = lean_usize_dec_eq(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_dec_ref(v_code_2346_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2574_);
lean_ctor_set(v___x_2704_, 1, v_a_2669_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2704_);
v___x_2706_ = v___x_2692_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_a_2669_);
lean_dec_ref(v___y_2574_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_code_2346_);
v___x_2709_ = v___x_2692_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_code_2346_);
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
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_a_2669_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2713_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2690_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2690_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_a_2669_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2721_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2670_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2670_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
return v___x_2668_;
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2729_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2642_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2642_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2737_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2622_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2622_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2745_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2600_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2600_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2753_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2593_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2593_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_code_2346_);
v_a_2761_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2578_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2578_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
v___jp_2769_:
{
uint8_t v___x_2784_; 
v___x_2784_ = l_Lean_Expr_isErased(v_type_2775_);
lean_dec_ref(v_type_2775_);
if (v___x_2784_ == 0)
{
lean_dec(v_value_2776_);
lean_dec(v_fvarId_2774_);
v___y_2568_ = v___y_2771_;
v___y_2569_ = v___y_2777_;
v___y_2570_ = v___y_2778_;
v___y_2571_ = v___y_2781_;
v___y_2572_ = v___y_2772_;
v___y_2573_ = v___y_2783_;
v___y_2574_ = v_decl_2773_;
v___y_2575_ = v___y_2779_;
v___y_2576_ = v___y_2782_;
v___y_2577_ = v___y_2780_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_box(1);
v___x_2786_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2770_, v_value_2776_, v___x_2785_);
lean_dec(v_value_2776_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_subst_2789_; lean_object* v_used_2790_; lean_object* v_binderRenaming_2791_; lean_object* v_funDeclInfoMap_2792_; uint8_t v_simplified_2793_; lean_object* v_visited_2794_; lean_object* v_inline_2795_; lean_object* v_inlineLocal_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_code_2346_);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_st_ref_take(v___y_2778_);
v_subst_2789_ = lean_ctor_get(v___x_2788_, 0);
v_used_2790_ = lean_ctor_get(v___x_2788_, 1);
v_binderRenaming_2791_ = lean_ctor_get(v___x_2788_, 2);
v_funDeclInfoMap_2792_ = lean_ctor_get(v___x_2788_, 3);
v_simplified_2793_ = lean_ctor_get_uint8(v___x_2788_, sizeof(void*)*7);
v_visited_2794_ = lean_ctor_get(v___x_2788_, 4);
v_inline_2795_ = lean_ctor_get(v___x_2788_, 5);
v_inlineLocal_2796_ = lean_ctor_get(v___x_2788_, 6);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2798_ = v___x_2788_;
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_inlineLocal_2796_);
lean_inc(v_inline_2795_);
lean_inc(v_visited_2794_);
lean_inc(v_funDeclInfoMap_2792_);
lean_inc(v_binderRenaming_2791_);
lean_inc(v_used_2790_);
lean_inc(v_subst_2789_);
lean_dec(v___x_2788_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2789_, v_fvarId_2774_, v___x_2787_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_used_2790_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_binderRenaming_2791_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_funDeclInfoMap_2792_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_visited_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_inline_2795_);
lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_inlineLocal_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2814_, sizeof(void*)*7, v_simplified_2793_);
v___x_2802_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_st_ref_put(v___y_2778_, v___x_2802_);
v___x_2804_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2773_, v___y_2778_, v___y_2781_);
lean_dec_ref(v_decl_2773_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_dec_ref_known(v___x_2804_, 1);
v_code_2346_ = v___y_2772_;
v_a_2347_ = v___y_2777_;
v_a_2348_ = v___y_2778_;
v_a_2349_ = v___y_2779_;
v_a_2350_ = v___y_2780_;
v_a_2351_ = v___y_2781_;
v_a_2352_ = v___y_2782_;
v_a_2353_ = v___y_2783_;
goto _start;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___y_2772_);
v_a_2806_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2804_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2804_);
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
}
}
else
{
lean_dec(v_fvarId_2774_);
v___y_2568_ = v___y_2771_;
v___y_2569_ = v___y_2777_;
v___y_2570_ = v___y_2778_;
v___y_2571_ = v___y_2781_;
v___y_2572_ = v___y_2772_;
v___y_2573_ = v___y_2783_;
v___y_2574_ = v_decl_2773_;
v___y_2575_ = v___y_2779_;
v___y_2576_ = v___y_2782_;
v___y_2577_ = v___y_2780_;
goto v___jp_2567_;
}
}
}
v___jp_2816_:
{
lean_object* v_fvarId_2828_; lean_object* v_type_2829_; lean_object* v_value_2830_; lean_object* v___x_2831_; 
v_fvarId_2828_ = lean_ctor_get(v___y_2819_, 0);
v_type_2829_ = lean_ctor_get(v___y_2819_, 2);
v_value_2830_ = lean_ctor_get(v___y_2819_, 3);
lean_inc(v_value_2830_);
v___x_2831_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2830_, v___y_2821_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2834_; 
v_val_2833_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_a_2832_, 1);
v___x_2834_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2822_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref_known(v___x_2834_, 1);
v___x_2835_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2817_, v___y_2819_, v_val_2833_, v___y_2825_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v_fvarId_2837_; lean_object* v_type_2838_; lean_object* v_value_2839_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v_fvarId_2837_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_fvarId_2837_);
v_type_2838_ = lean_ctor_get(v_a_2836_, 2);
lean_inc_ref(v_type_2838_);
v_value_2839_ = lean_ctor_get(v_a_2836_, 3);
lean_inc(v_value_2839_);
v___y_2770_ = v___y_2817_;
v___y_2771_ = v___y_2818_;
v___y_2772_ = v___y_2820_;
v_decl_2773_ = v_a_2836_;
v_fvarId_2774_ = v_fvarId_2837_;
v_type_2775_ = v_type_2838_;
v_value_2776_ = v_value_2839_;
v___y_2777_ = v___y_2821_;
v___y_2778_ = v___y_2822_;
v___y_2779_ = v___y_2823_;
v___y_2780_ = v___y_2824_;
v___y_2781_ = v___y_2825_;
v___y_2782_ = v___y_2826_;
v___y_2783_ = v___y_2827_;
goto v___jp_2769_;
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v___y_2826_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_code_2346_);
v_a_2840_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2835_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2835_);
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
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_val_2833_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_code_2346_);
v_a_2848_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2834_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2834_);
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
else
{
lean_inc(v_value_2830_);
lean_inc_ref(v_type_2829_);
lean_inc(v_fvarId_2828_);
lean_dec(v_a_2832_);
v___y_2770_ = v___y_2817_;
v___y_2771_ = v___y_2818_;
v___y_2772_ = v___y_2820_;
v_decl_2773_ = v___y_2819_;
v_fvarId_2774_ = v_fvarId_2828_;
v_type_2775_ = v_type_2829_;
v_value_2776_ = v_value_2830_;
v___y_2777_ = v___y_2821_;
v___y_2778_ = v___y_2822_;
v___y_2779_ = v___y_2823_;
v___y_2780_ = v___y_2824_;
v___y_2781_ = v___y_2825_;
v___y_2782_ = v___y_2826_;
v___y_2783_ = v___y_2827_;
goto v___jp_2769_;
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v___y_2826_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_code_2346_);
v_a_2856_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2831_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2831_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
v___jp_2864_:
{
uint8_t v___x_2869_; 
v___x_2869_ = l_Lean_instBEqFVarId_beq(v___y_2865_, v___y_2866_);
lean_dec(v___y_2865_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref(v___y_2867_);
lean_dec_ref(v_code_2346_);
v___x_2870_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___y_2866_);
lean_ctor_set(v___x_2870_, 1, v___y_2868_);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
else
{
size_t v___x_2872_; size_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = lean_ptr_addr(v___y_2867_);
lean_dec_ref(v___y_2867_);
v___x_2873_ = lean_ptr_addr(v___y_2868_);
v___x_2874_ = lean_usize_dec_eq(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_code_2346_);
v___x_2875_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___y_2866_);
lean_ctor_set(v___x_2875_, 1, v___y_2868_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; 
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2866_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_code_2346_);
return v___x_2877_;
}
}
}
v___jp_2878_:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v___x_2881_, 0);
lean_dec(v_unused_2890_);
v___x_2883_ = v___x_2881_;
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
else
{
lean_dec(v___x_2881_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2889_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2885_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___y_2879_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2885_);
v___x_2887_ = v___x_2883_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v___y_2879_);
v_a_2891_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2881_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2881_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
v___jp_2899_:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_nat_dec_lt(v___y_2901_, v___y_2907_);
lean_dec(v___y_2901_);
if (v___x_2909_ == 0)
{
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v___y_2903_);
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2906_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2910_; size_t v___x_2911_; size_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_box(0);
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = lean_usize_of_nat(v___y_2907_);
lean_dec(v___y_2907_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2903_, v___x_2911_, v___x_2912_, v___x_2910_, v___y_2905_, v___y_2902_, v___y_2904_, v___y_2908_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v___y_2903_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2906_;
goto v___jp_2878_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___y_2900_);
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
v___jp_2922_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2927_, 0, v___y_2926_);
lean_ctor_set(v___x_2927_, 1, v___y_2923_);
lean_ctor_set(v___x_2927_, 2, v___y_2924_);
lean_ctor_set(v___x_2927_, 3, v___y_2925_);
v___x_2928_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
v___jp_2930_:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v___y_2935_);
v___x_2945_ = lean_nat_dec_lt(v___y_2931_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v_code_2346_);
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2931_;
v___y_2902_ = v___y_2941_;
v___y_2903_ = v___y_2935_;
v___y_2904_ = v___y_2942_;
v___y_2905_ = v___y_2940_;
v___y_2906_ = v___y_2939_;
v___y_2907_ = v___x_2944_;
v___y_2908_ = v___y_2943_;
goto v___jp_2899_;
}
else
{
if (v___x_2945_ == 0)
{
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v_code_2346_);
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2931_;
v___y_2902_ = v___y_2941_;
v___y_2903_ = v___y_2935_;
v___y_2904_ = v___y_2942_;
v___y_2905_ = v___y_2940_;
v___y_2906_ = v___y_2939_;
v___y_2907_ = v___x_2944_;
v___y_2908_ = v___y_2943_;
goto v___jp_2899_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2944_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2935_, v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v_code_2346_);
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2931_;
v___y_2902_ = v___y_2941_;
v___y_2903_ = v___y_2935_;
v___y_2904_ = v___y_2942_;
v___y_2905_ = v___y_2940_;
v___y_2906_ = v___y_2939_;
v___y_2907_ = v___x_2944_;
v___y_2908_ = v___y_2943_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2949_; 
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2931_);
lean_inc(v___y_2933_);
v___x_2949_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2933_, v___y_2939_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2963_; 
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2963_ == 0)
{
lean_object* v_unused_2964_; 
v_unused_2964_ = lean_ctor_get(v___x_2949_, 0);
lean_dec(v_unused_2964_);
v___x_2951_ = v___x_2949_;
v_isShared_2952_ = v_isSharedCheck_2963_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v___x_2949_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2963_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
size_t v___x_2953_; size_t v___x_2954_; uint8_t v___x_2955_; 
v___x_2953_ = lean_ptr_addr(v___y_2937_);
lean_dec_ref(v___y_2937_);
v___x_2954_ = lean_ptr_addr(v___y_2935_);
v___x_2955_ = lean_usize_dec_eq(v___x_2953_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_del_object(v___x_2951_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec_ref(v_code_2346_);
v___y_2923_ = v___y_2932_;
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2935_;
v___y_2926_ = v___y_2938_;
goto v___jp_2922_;
}
else
{
size_t v___x_2956_; size_t v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_ptr_addr(v___y_2936_);
lean_dec_ref(v___y_2936_);
v___x_2957_ = lean_ptr_addr(v___y_2932_);
v___x_2958_ = lean_usize_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_del_object(v___x_2951_);
lean_dec(v___y_2934_);
lean_dec_ref(v_code_2346_);
v___y_2923_ = v___y_2932_;
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2935_;
v___y_2926_ = v___y_2938_;
goto v___jp_2922_;
}
else
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Lean_instBEqFVarId_beq(v___y_2934_, v___y_2933_);
lean_dec(v___y_2934_);
if (v___x_2959_ == 0)
{
lean_del_object(v___x_2951_);
lean_dec_ref(v_code_2346_);
v___y_2923_ = v___y_2932_;
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2935_;
v___y_2926_ = v___y_2938_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2961_; 
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v_code_2346_);
v___x_2961_ = v___x_2951_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_code_2346_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v_code_2346_);
v_a_2965_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2949_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2949_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
}
v___jp_2973_:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2974_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v___x_2976_, 0);
lean_dec(v_unused_2984_);
v___x_2978_ = v___x_2976_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v___x_2976_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___y_2975_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___y_2975_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v___y_2975_);
v_a_2985_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2976_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2976_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
v___jp_2993_:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_nat_dec_lt(v___y_2994_, v___y_2998_);
lean_dec(v___y_2994_);
if (v___x_3000_ == 0)
{
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
v___y_2974_ = v___y_2997_;
v___y_2975_ = v___y_2999_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___y_2998_);
lean_dec(v___y_2998_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_2995_, v___x_3002_, v___x_3003_, v___x_3001_, v___y_2996_);
lean_dec_ref(v___y_2995_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_dec_ref_known(v___x_3004_, 1);
v___y_2974_ = v___y_2997_;
v___y_2975_ = v___y_2999_;
goto v___jp_2973_;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v___y_2999_);
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
v___jp_3013_:
{
switch(lean_obj_tag(v_code_2346_))
{
case 0:
{
lean_object* v_decl_3021_; lean_object* v_k_3022_; uint8_t v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; 
v_decl_3021_ = lean_ctor_get(v_code_2346_, 0);
v_k_3022_ = lean_ctor_get(v_code_2346_, 1);
v___x_3023_ = 0;
v___x_3024_ = 0;
lean_inc_ref(v_decl_3021_);
v___x_3025_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3023_, v___x_3024_, v_decl_3021_, v___y_3015_, v___y_3018_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; uint8_t v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3023_, v_decl_3021_, v_a_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3015_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
lean_inc_ref(v_k_3022_);
lean_inc_ref(v_decl_3021_);
v___y_2817_ = v___x_3023_;
v___y_2818_ = v_decl_3021_;
v___y_2819_ = v_a_3026_;
v___y_2820_ = v_k_3022_;
v___y_2821_ = v___y_3014_;
v___y_2822_ = v___y_3015_;
v___y_2823_ = v___y_3016_;
v___y_2824_ = v___y_3017_;
v___y_2825_ = v___y_3018_;
v___y_2826_ = v___y_3019_;
v___y_2827_ = v___y_3020_;
goto v___jp_2816_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_a_3026_);
lean_dec_ref_known(v_code_2346_, 2);
lean_dec_ref(v___y_3019_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_inc_ref(v_k_3022_);
lean_inc_ref(v_decl_3021_);
v___y_2817_ = v___x_3023_;
v___y_2818_ = v_decl_3021_;
v___y_2819_ = v_a_3026_;
v___y_2820_ = v_k_3022_;
v___y_2821_ = v___y_3014_;
v___y_2822_ = v___y_3015_;
v___y_2823_ = v___y_3016_;
v___y_2824_ = v___y_3017_;
v___y_2825_ = v___y_3018_;
v___y_2826_ = v___y_3019_;
v___y_2827_ = v___y_3020_;
goto v___jp_2816_;
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref_known(v_code_2346_, 2);
lean_dec_ref(v___y_3019_);
v_a_3037_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3025_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3025_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3045_; lean_object* v_args_3046_; uint8_t v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v_subst_3050_; lean_object* v___x_3051_; 
v_fvarId_3045_ = lean_ctor_get(v_code_2346_, 0);
v_args_3046_ = lean_ctor_get(v_code_2346_, 1);
v___x_3047_ = 0;
v___x_3048_ = 0;
v___x_3049_ = lean_st_ref_get(v___y_3015_);
v_subst_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc_ref(v_subst_3050_);
lean_dec(v___x_3049_);
lean_inc(v_fvarId_3045_);
v___x_3051_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3050_, v_fvarId_3045_, v___x_3048_);
lean_dec_ref(v_subst_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_fvarId_3052_; lean_object* v___x_3053_; 
v_fvarId_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_fvarId_3052_);
lean_dec_ref_known(v___x_3051_, 1);
lean_inc_ref(v_args_3046_);
v___x_3053_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3047_, v___x_3048_, v_args_3046_, v___y_3015_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc_n(v_a_3054_, 2);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3052_, v_a_3054_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
if (lean_obj_tag(v_a_3056_) == 1)
{
lean_object* v_val_3057_; 
lean_dec(v_a_3054_);
lean_dec(v_fvarId_3052_);
lean_dec_ref_known(v_code_2346_, 2);
v_val_3057_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v_a_3056_, 1);
v_code_2346_ = v_val_3057_;
v_a_2347_ = v___y_3014_;
v_a_2348_ = v___y_3015_;
v_a_2349_ = v___y_3016_;
v_a_2350_ = v___y_3017_;
v_a_2351_ = v___y_3018_;
v_a_2352_ = v___y_3019_;
v_a_2353_ = v___y_3020_;
goto _start;
}
else
{
lean_object* v___x_3059_; 
lean_dec(v_a_3056_);
lean_dec_ref(v___y_3019_);
lean_inc(v_fvarId_3052_);
v___x_3059_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3052_, v___y_3015_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
lean_dec_ref_known(v___x_3059_, 1);
v___x_3060_ = lean_unsigned_to_nat(0u);
v___x_3061_ = lean_array_get_size(v_a_3054_);
v___x_3062_ = lean_nat_dec_lt(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_inc_ref(v_args_3046_);
lean_inc(v_fvarId_3045_);
v___y_2865_ = v_fvarId_3045_;
v___y_2866_ = v_fvarId_3052_;
v___y_2867_ = v_args_3046_;
v___y_2868_ = v_a_3054_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_3063_; size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3063_ = lean_box(0);
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = lean_usize_of_nat(v___x_3061_);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3054_, v___x_3064_, v___x_3065_, v___x_3063_, v___y_3015_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_dec_ref_known(v___x_3066_, 1);
lean_inc_ref(v_args_3046_);
lean_inc(v_fvarId_3045_);
v___y_2865_ = v_fvarId_3045_;
v___y_2866_ = v_fvarId_3052_;
v___y_2867_ = v_args_3046_;
v___y_2868_ = v_a_3054_;
goto v___jp_2864_;
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3054_);
lean_dec(v_fvarId_3052_);
lean_dec_ref_known(v_code_2346_, 2);
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_3054_);
lean_dec(v_fvarId_3052_);
lean_dec_ref_known(v_code_2346_, 2);
v_a_3075_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3059_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3059_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_a_3054_);
lean_dec(v_fvarId_3052_);
lean_dec_ref_known(v_code_2346_, 2);
lean_dec_ref(v___y_3019_);
v_a_3083_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3055_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3055_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_fvarId_3052_);
lean_dec_ref_known(v_code_2346_, 2);
lean_dec_ref(v___y_3019_);
v_a_3091_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3053_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3053_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v___x_3099_; 
lean_dec_ref_known(v_code_2346_, 2);
v___x_3099_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3047_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec_ref(v___y_3019_);
return v___x_3099_;
}
}
case 4:
{
lean_object* v_cases_3100_; lean_object* v___x_3101_; 
v_cases_3100_ = lean_ctor_get(v_code_2346_, 0);
lean_inc_ref(v_cases_3100_);
v___x_3101_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3100_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3174_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3174_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3174_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
if (lean_obj_tag(v_a_3102_) == 1)
{
lean_object* v_val_3106_; lean_object* v___x_3108_; 
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_val_3106_ = lean_ctor_get(v_a_3102_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v_a_3102_, 1);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v_val_3106_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_val_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
else
{
lean_object* v_typeName_3110_; lean_object* v_resultType_3111_; lean_object* v_discr_3112_; lean_object* v_alts_3113_; uint8_t v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v_subst_3117_; lean_object* v___x_3118_; 
lean_del_object(v___x_3104_);
lean_dec(v_a_3102_);
v_typeName_3110_ = lean_ctor_get(v_cases_3100_, 0);
v_resultType_3111_ = lean_ctor_get(v_cases_3100_, 1);
v_discr_3112_ = lean_ctor_get(v_cases_3100_, 2);
v_alts_3113_ = lean_ctor_get(v_cases_3100_, 3);
v___x_3114_ = 0;
v___x_3115_ = 0;
v___x_3116_ = lean_st_ref_get(v___y_3015_);
v_subst_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc_ref(v_subst_3117_);
lean_dec(v___x_3116_);
lean_inc(v_discr_3112_);
v___x_3118_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3117_, v_discr_3112_, v___x_3115_);
lean_dec_ref(v_subst_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_fvarId_3119_; lean_object* v___x_3120_; lean_object* v_subst_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_fvarId_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_n(v_fvarId_3119_, 2);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3120_ = lean_st_ref_get(v___y_3015_);
v_subst_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_subst_3121_);
lean_dec(v___x_3120_);
lean_inc_ref(v_resultType_3111_);
v___x_3122_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3114_, v_subst_3121_, v___x_3115_, v_resultType_3111_);
lean_dec_ref(v_subst_3121_);
v___x_3123_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3113_);
v___x_3124_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3119_, v___x_3123_, v_alts_3113_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3126_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3124_, 1);
v___x_3126_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3125_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3156_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3156_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3156_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_array_get_size(v_a_3127_);
v___x_3132_ = lean_unsigned_to_nat(1u);
v___x_3133_ = lean_nat_dec_eq(v___x_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_del_object(v___x_3129_);
lean_inc(v_typeName_3110_);
lean_inc_ref(v_alts_3113_);
lean_inc_ref(v_resultType_3111_);
lean_inc(v_discr_3112_);
v___y_2931_ = v___x_3123_;
v___y_2932_ = v___x_3122_;
v___y_2933_ = v_fvarId_3119_;
v___y_2934_ = v_discr_3112_;
v___y_2935_ = v_a_3127_;
v___y_2936_ = v_resultType_3111_;
v___y_2937_ = v_alts_3113_;
v___y_2938_ = v_typeName_3110_;
v___y_2939_ = v___y_3015_;
v___y_2940_ = v___y_3017_;
v___y_2941_ = v___y_3018_;
v___y_2942_ = v___y_3019_;
v___y_2943_ = v___y_3020_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_array_fget_borrowed(v_a_3127_, v___x_3123_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_params_3135_; lean_object* v_code_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
lean_del_object(v___x_3129_);
v_params_3135_ = lean_ctor_get(v___x_3134_, 1);
v_code_3136_ = lean_ctor_get(v___x_3134_, 2);
v___x_3137_ = lean_array_get_size(v_params_3135_);
v___x_3138_ = lean_nat_dec_lt(v___x_3123_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_inc_ref(v_code_3136_);
lean_inc_ref(v_params_3135_);
lean_dec(v_a_3127_);
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v___y_2994_ = v___x_3123_;
v___y_2995_ = v_params_3135_;
v___y_2996_ = v___y_3018_;
v___y_2997_ = v___y_3015_;
v___y_2998_ = v___x_3137_;
v___y_2999_ = v_code_3136_;
goto v___jp_2993_;
}
else
{
if (v___x_3138_ == 0)
{
lean_inc_ref(v_code_3136_);
lean_inc_ref(v_params_3135_);
lean_dec(v_a_3127_);
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v___y_2994_ = v___x_3123_;
v___y_2995_ = v_params_3135_;
v___y_2996_ = v___y_3018_;
v___y_2997_ = v___y_3015_;
v___y_2998_ = v___x_3137_;
v___y_2999_ = v_code_3136_;
goto v___jp_2993_;
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((size_t)0ULL);
v___x_3140_ = lean_usize_of_nat(v___x_3137_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3135_, v___x_3139_, v___x_3140_, v___y_3015_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; uint8_t v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v___x_3143_ = lean_unbox(v_a_3142_);
lean_dec(v_a_3142_);
if (v___x_3143_ == 0)
{
lean_inc_ref(v_code_3136_);
lean_inc_ref(v_params_3135_);
lean_dec(v_a_3127_);
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v___y_2994_ = v___x_3123_;
v___y_2995_ = v_params_3135_;
v___y_2996_ = v___y_3018_;
v___y_2997_ = v___y_3015_;
v___y_2998_ = v___x_3137_;
v___y_2999_ = v_code_3136_;
goto v___jp_2993_;
}
else
{
lean_inc(v_typeName_3110_);
lean_inc_ref(v_alts_3113_);
lean_inc_ref(v_resultType_3111_);
lean_inc(v_discr_3112_);
v___y_2931_ = v___x_3123_;
v___y_2932_ = v___x_3122_;
v___y_2933_ = v_fvarId_3119_;
v___y_2934_ = v_discr_3112_;
v___y_2935_ = v_a_3127_;
v___y_2936_ = v_resultType_3111_;
v___y_2937_ = v_alts_3113_;
v___y_2938_ = v_typeName_3110_;
v___y_2939_ = v___y_3015_;
v___y_2940_ = v___y_3017_;
v___y_2941_ = v___y_3018_;
v___y_2942_ = v___y_3019_;
v___y_2943_ = v___y_3020_;
goto v___jp_2930_;
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3127_);
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_a_3144_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3141_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3141_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
else
{
lean_object* v_code_3152_; lean_object* v___x_3154_; 
lean_inc_ref(v___x_3134_);
lean_dec(v_a_3127_);
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_code_3152_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_ref(v_code_3152_);
lean_dec_ref_known(v___x_3134_, 1);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v_code_3152_);
v___x_3154_ = v___x_3129_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_code_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_a_3157_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3126_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3126_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v___x_3122_);
lean_dec(v_fvarId_3119_);
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_a_3165_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3124_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3124_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v___x_3173_; 
lean_dec_ref_known(v_code_2346_, 1);
v___x_3173_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3114_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec_ref(v___y_3019_);
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref_known(v_code_2346_, 1);
lean_dec_ref(v___y_3019_);
v_a_3175_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3101_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3101_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_3183_; uint8_t v___x_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v_subst_3187_; lean_object* v___x_3188_; 
v_fvarId_3183_ = lean_ctor_get(v_code_2346_, 0);
v___x_3184_ = 0;
v___x_3185_ = 0;
v___x_3186_ = lean_st_ref_get(v___y_3015_);
v_subst_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc_ref(v_subst_3187_);
lean_dec(v___x_3186_);
lean_inc(v_fvarId_3183_);
v___x_3188_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3187_, v_fvarId_3183_, v___x_3185_);
lean_dec_ref(v_subst_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_fvarId_3189_; lean_object* v___x_3190_; 
lean_dec_ref(v___y_3019_);
v_fvarId_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc_n(v_fvarId_3189_, 2);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3189_, v___y_3015_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3209_; 
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3210_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3209_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3209_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
uint8_t v___x_3194_; 
v___x_3194_ = l_Lean_instBEqFVarId_beq(v_fvarId_3183_, v_fvarId_3189_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3204_; 
v_isSharedCheck_3204_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_3205_);
v___x_3196_ = v_code_2346_;
v_isShared_3197_ = v_isSharedCheck_3204_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v_code_2346_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3204_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v_fvarId_3189_);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_fvarId_3189_);
v___x_3199_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3199_);
v___x_3201_ = v___x_3192_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v___x_3207_; 
lean_dec(v_fvarId_3189_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_code_2346_);
v___x_3207_ = v___x_3192_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_code_2346_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_fvarId_3189_);
lean_dec_ref_known(v_code_2346_, 1);
v_a_3211_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3190_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3190_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v___x_3219_; 
lean_dec_ref_known(v_code_2346_, 1);
v___x_3219_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3184_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec_ref(v___y_3019_);
return v___x_3219_;
}
}
case 6:
{
lean_object* v_type_3220_; uint8_t v___x_3221_; uint8_t v___x_3222_; lean_object* v___x_3223_; lean_object* v_subst_3224_; lean_object* v___x_3225_; size_t v___x_3226_; size_t v___x_3227_; uint8_t v___x_3228_; 
lean_dec_ref(v___y_3019_);
v_type_3220_ = lean_ctor_get(v_code_2346_, 0);
v___x_3221_ = 0;
v___x_3222_ = 0;
v___x_3223_ = lean_st_ref_get(v___y_3015_);
v_subst_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc_ref(v_subst_3224_);
lean_dec(v___x_3223_);
lean_inc_ref(v_type_3220_);
v___x_3225_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3221_, v_subst_3224_, v___x_3222_, v_type_3220_);
lean_dec_ref(v_subst_3224_);
v___x_3226_ = lean_ptr_addr(v_type_3220_);
v___x_3227_ = lean_ptr_addr(v___x_3225_);
v___x_3228_ = lean_usize_dec_eq(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v_code_2346_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_code_2346_, 0);
lean_dec(v_unused_3237_);
v___x_3230_ = v_code_2346_;
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
else
{
lean_dec(v_code_2346_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3236_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3225_);
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3225_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
}
else
{
lean_object* v___x_3238_; 
lean_dec_ref(v___x_3225_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_code_2346_);
return v___x_3238_;
}
}
default: 
{
lean_object* v_decl_3239_; lean_object* v_k_3240_; 
v_decl_3239_ = lean_ctor_get(v_code_2346_, 0);
v_k_3240_ = lean_ctor_get(v_code_2346_, 1);
lean_inc_ref(v_k_3240_);
lean_inc_ref(v_decl_3239_);
v_decl_2492_ = v_decl_3239_;
v_k_2493_ = v_k_3240_;
v___y_2494_ = v___y_3014_;
v___y_2495_ = v___y_3015_;
v___y_2496_ = v___y_3016_;
v___y_2497_ = v___y_3017_;
v___y_2498_ = v___y_3018_;
v___y_2499_ = v___y_3019_;
v___y_2500_ = v___y_3020_;
goto v___jp_2491_;
}
}
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_nat_add(v_currRecDepth_3242_, v___x_3248_);
lean_dec(v_currRecDepth_3242_);
v___x_3250_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3250_, 0, v_toCold_3241_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
lean_ctor_set(v___x_3250_, 2, v_ref_3243_);
lean_ctor_set_uint16(v___x_3250_, sizeof(void*)*3, v_optionFlags_3244_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*3 + 2, v_suppressElabErrors_3245_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*3 + 3, v_isRecordingDeps_3246_);
v___x_3251_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2348_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v___x_3252_; lean_object* v_visited_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
lean_dec_ref_known(v___x_3251_, 1);
v___x_3252_ = lean_st_ref_get(v_a_2348_);
v_visited_3253_ = lean_ctor_get(v___x_3252_, 4);
lean_inc(v_visited_3253_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_unsigned_to_nat(128u);
v___x_3255_ = lean_nat_mod(v_visited_3253_, v___x_3254_);
lean_dec(v_visited_3253_);
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_nat_dec_eq(v___x_3255_, v___x_3256_);
lean_dec(v___x_3255_);
if (v___x_3257_ == 0)
{
v___y_3014_ = v_a_2347_;
v___y_3015_ = v_a_2348_;
v___y_3016_ = v_a_2349_;
v___y_3017_ = v_a_2350_;
v___y_3018_ = v_a_2351_;
v___y_3019_ = v___x_3250_;
v___y_3020_ = v_a_2353_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__4));
v___x_3259_ = l_Lean_Core_checkSystem(v___x_3258_, v___x_3250_, v_a_2353_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_dec_ref_known(v___x_3259_, 1);
v___y_3014_ = v_a_2347_;
v___y_3015_ = v_a_2348_;
v___y_3016_ = v_a_2349_;
v___y_3017_ = v_a_2350_;
v___y_3018_ = v_a_2351_;
v___y_3019_ = v___x_3250_;
v___y_3020_ = v_a_2353_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref_known(v___x_3250_, 3);
lean_dec_ref(v_code_2346_);
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref_known(v___x_3250_, 3);
lean_dec_ref(v_code_2346_);
v_a_3268_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3251_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3251_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_params_3290_; lean_object* v_type_3291_; lean_object* v_value_3292_; uint8_t v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v_subst_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_params_3290_ = lean_ctor_get(v_decl_3281_, 2);
v_type_3291_ = lean_ctor_get(v_decl_3281_, 3);
v_value_3292_ = lean_ctor_get(v_decl_3281_, 4);
v___x_3293_ = 0;
v___x_3294_ = 0;
v___x_3295_ = lean_st_ref_get(v_a_3283_);
v_subst_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_subst_3296_);
lean_dec(v___x_3295_);
lean_inc_ref(v_type_3291_);
v___x_3297_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3293_, v_subst_3296_, v___x_3294_, v_type_3291_);
lean_dec_ref(v_subst_3296_);
lean_inc_ref(v_params_3290_);
v___x_3298_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3293_, v___x_3294_, v_params_3290_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
lean_inc_ref(v_a_3287_);
lean_inc_ref(v_value_3292_);
v___x_3300_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3292_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3302_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v___x_3302_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3293_, v_decl_3281_, v___x_3297_, v_a_3299_, v_a_3301_, v_a_3286_);
return v___x_3302_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3299_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v_decl_3281_);
v_a_3303_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3300_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3300_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v___x_3297_);
lean_dec_ref(v_decl_3281_);
v_a_3311_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3298_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3298_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3329_, lean_object* v_i_3330_, lean_object* v_as_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3329_, v_i_3330_, v_as_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3351_, lean_object* v_k_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3351_, v_k_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3372_, uint8_t v_t_3373_, lean_object* v_decl_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3372_, v_t_3373_, v_decl_3374_, v___y_3376_, v___y_3379_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3384_, lean_object* v_t_3385_, lean_object* v_decl_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_pu_boxed_3395_; uint8_t v_t_boxed_3396_; lean_object* v_res_3397_; 
v_pu_boxed_3395_ = lean_unbox(v_pu_3384_);
v_t_boxed_3396_ = lean_unbox(v_t_3385_);
v_res_3397_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3395_, v_t_boxed_3396_, v_decl_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3398_, uint8_t v_t_3399_, lean_object* v_args_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3398_, v_t_3399_, v_args_3400_, v___y_3402_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3410_, lean_object* v_t_3411_, lean_object* v_args_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v_pu_boxed_3421_; uint8_t v_t_boxed_3422_; lean_object* v_res_3423_; 
v_pu_boxed_3421_ = lean_unbox(v_pu_3410_);
v_t_boxed_3422_ = lean_unbox(v_t_3411_);
v_res_3423_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3421_, v_t_boxed_3422_, v_args_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3424_, lean_object* v_R_3425_, lean_object* v_a_3426_, lean_object* v_b_3427_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3426_, v_b_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_, lean_object* v_x_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3430_, v_x_3431_, v_x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3434_, size_t v_i_3435_, size_t v_stop_3436_, lean_object* v_b_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3434_, v_i_3435_, v_stop_3436_, v_b_3437_, v___y_3439_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3447_, lean_object* v_i_3448_, lean_object* v_stop_3449_, lean_object* v_b_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
size_t v_i_boxed_3459_; size_t v_stop_boxed_3460_; lean_object* v_res_3461_; 
v_i_boxed_3459_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_stop_boxed_3460_ = lean_unbox_usize(v_stop_3449_);
lean_dec(v_stop_3449_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3447_, v_i_boxed_3459_, v_stop_boxed_3460_, v_b_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v_as_3447_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3462_, size_t v_i_3463_, size_t v_stop_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3462_, v_i_3463_, v_stop_3464_, v___y_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3474_, lean_object* v_i_3475_, lean_object* v_stop_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
size_t v_i_boxed_3485_; size_t v_stop_boxed_3486_; lean_object* v_res_3487_; 
v_i_boxed_3485_ = lean_unbox_usize(v_i_3475_);
lean_dec(v_i_3475_);
v_stop_boxed_3486_ = lean_unbox_usize(v_stop_3476_);
lean_dec(v_stop_3476_);
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3474_, v_i_boxed_3485_, v_stop_boxed_3486_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec_ref(v_as_3474_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3488_, size_t v_i_3489_, size_t v_stop_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3488_, v_i_3489_, v_stop_3490_, v_b_3491_, v___y_3493_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3498_, lean_object* v_i_3499_, lean_object* v_stop_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
size_t v_i_boxed_3507_; size_t v_stop_boxed_3508_; lean_object* v_res_3509_; 
v_i_boxed_3507_ = lean_unbox_usize(v_i_3499_);
lean_dec(v_i_3499_);
v_stop_boxed_3508_ = lean_unbox_usize(v_stop_3500_);
lean_dec(v_stop_3500_);
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3498_, v_i_boxed_3507_, v_stop_boxed_3508_, v_b_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v_as_3498_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3510_, size_t v_i_3511_, size_t v_stop_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3510_, v_i_3511_, v_stop_3512_, v_b_3513_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3523_, lean_object* v_i_3524_, lean_object* v_stop_3525_, lean_object* v_b_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
size_t v_i_boxed_3535_; size_t v_stop_boxed_3536_; lean_object* v_res_3537_; 
v_i_boxed_3535_ = lean_unbox_usize(v_i_3524_);
lean_dec(v_i_3524_);
v_stop_boxed_3536_ = lean_unbox_usize(v_stop_3525_);
lean_dec(v_stop_3525_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3523_, v_i_boxed_3535_, v_stop_boxed_3536_, v_b_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec_ref(v_as_3523_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3538_, size_t v_i_3539_, size_t v_stop_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3538_, v_i_3539_, v_stop_3540_, v_b_3541_, v___y_3546_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3551_, lean_object* v_i_3552_, lean_object* v_stop_3553_, lean_object* v_b_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
size_t v_i_boxed_3563_; size_t v_stop_boxed_3564_; lean_object* v_res_3565_; 
v_i_boxed_3563_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_stop_boxed_3564_ = lean_unbox_usize(v_stop_3553_);
lean_dec(v_stop_3553_);
v_res_3565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3551_, v_i_boxed_3563_, v_stop_boxed_3564_, v_b_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v_as_3551_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3566_, size_t v_i_3567_, size_t v_stop_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3566_, v_i_3567_, v_stop_3568_, v___y_3570_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3578_, lean_object* v_i_3579_, lean_object* v_stop_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
size_t v_i_boxed_3589_; size_t v_stop_boxed_3590_; lean_object* v_res_3591_; 
v_i_boxed_3589_ = lean_unbox_usize(v_i_3579_);
lean_dec(v_i_3579_);
v_stop_boxed_3590_ = lean_unbox_usize(v_stop_3580_);
lean_dec(v_stop_3580_);
v_res_3591_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3578_, v_i_boxed_3589_, v_stop_boxed_3590_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v_as_3578_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3592_, size_t v_sz_3593_, size_t v_i_3594_, lean_object* v_b_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3592_, v_sz_3593_, v_i_3594_, v_b_3595_, v___y_3597_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3605_, lean_object* v_sz_3606_, lean_object* v_i_3607_, lean_object* v_b_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
size_t v_sz_boxed_3617_; size_t v_i_boxed_3618_; lean_object* v_res_3619_; 
v_sz_boxed_3617_ = lean_unbox_usize(v_sz_3606_);
lean_dec(v_sz_3606_);
v_i_boxed_3618_ = lean_unbox_usize(v_i_3607_);
lean_dec(v_i_3607_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3605_, v_sz_boxed_3617_, v_i_boxed_3618_, v_b_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_as_3605_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, size_t v_x_3622_, size_t v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3621_, v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
size_t v_x_47660__boxed_3633_; size_t v_x_47661__boxed_3634_; lean_object* v_res_3635_; 
v_x_47660__boxed_3633_ = lean_unbox_usize(v_x_3629_);
lean_dec(v_x_3629_);
v_x_47661__boxed_3634_ = lean_unbox_usize(v_x_3630_);
lean_dec(v_x_3630_);
v_res_3635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3627_, v_x_3628_, v_x_47660__boxed_3633_, v_x_47661__boxed_3634_, v_x_3631_, v_x_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3636_, uint8_t v_t_3637_, lean_object* v_i_3638_, lean_object* v_as_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3636_, v_t_3637_, v_i_3638_, v_as_3639_, v___y_3641_, v___y_3644_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3649_, lean_object* v_t_3650_, lean_object* v_i_3651_, lean_object* v_as_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
uint8_t v_pu_boxed_3661_; uint8_t v_t_boxed_3662_; lean_object* v_res_3663_; 
v_pu_boxed_3661_ = lean_unbox(v_pu_3649_);
v_t_boxed_3662_ = lean_unbox(v_t_3650_);
v_res_3663_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3661_, v_t_boxed_3662_, v_i_3651_, v_as_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3664_, lean_object* v_n_3665_, lean_object* v_k_3666_, lean_object* v_v_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3665_, v_k_3666_, v_v_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3669_, size_t v_depth_3670_, lean_object* v_keys_3671_, lean_object* v_vals_3672_, lean_object* v_heq_3673_, lean_object* v_i_3674_, lean_object* v_entries_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3670_, v_keys_3671_, v_vals_3672_, v_i_3674_, v_entries_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3677_, lean_object* v_depth_3678_, lean_object* v_keys_3679_, lean_object* v_vals_3680_, lean_object* v_heq_3681_, lean_object* v_i_3682_, lean_object* v_entries_3683_){
_start:
{
size_t v_depth_boxed_3684_; lean_object* v_res_3685_; 
v_depth_boxed_3684_ = lean_unbox_usize(v_depth_3678_);
lean_dec(v_depth_3678_);
v_res_3685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3677_, v_depth_boxed_3684_, v_keys_3679_, v_vals_3680_, v_heq_3681_, v_i_3682_, v_entries_3683_);
lean_dec_ref(v_vals_3680_);
lean_dec_ref(v_keys_3679_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3687_, v_x_3688_, v_x_3689_, v_x_3690_);
return v___x_3691_;
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
