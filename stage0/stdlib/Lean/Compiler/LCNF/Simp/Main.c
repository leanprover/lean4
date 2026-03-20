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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
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
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_k_4_);
lean_dec_ref(v_c_3_);
v_c_3_ = v_k_4_;
goto _start;
}
case 1:
{
lean_object* v_k_6_; 
v_k_6_ = lean_ctor_get(v_c_3_, 1);
lean_inc_ref(v_k_6_);
lean_dec_ref(v_c_3_);
v_c_3_ = v_k_6_;
goto _start;
}
case 4:
{
lean_object* v_cases_8_; lean_object* v_alts_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_cases_8_ = lean_ctor_get(v_c_3_, 0);
lean_inc_ref(v_cases_8_);
lean_dec_ref(v_c_3_);
v_alts_9_ = lean_ctor_get(v_cases_8_, 3);
lean_inc_ref(v_alts_9_);
lean_dec_ref(v_cases_8_);
v___x_10_ = lean_array_get_size(v_alts_9_);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_dec_eq(v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_dec_ref(v_alts_9_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_array_get(v___x_13_, v_alts_9_, v___x_14_);
lean_dec_ref(v_alts_9_);
switch(lean_obj_tag(v___x_15_))
{
case 0:
{
lean_object* v_code_16_; 
v_code_16_ = lean_ctor_get(v___x_15_, 2);
lean_inc_ref(v_code_16_);
lean_dec_ref(v___x_15_);
v_c_3_ = v_code_16_;
goto _start;
}
case 1:
{
lean_object* v_code_18_; 
v_code_18_ = lean_ctor_get(v___x_15_, 1);
lean_inc_ref(v_code_18_);
lean_dec_ref(v___x_15_);
v_c_3_ = v_code_18_;
goto _start;
}
default: 
{
lean_object* v_code_20_; 
v_code_20_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_code_20_);
lean_dec_ref(v___x_15_);
v_c_3_ = v_code_20_;
goto _start;
}
}
}
}
case 5:
{
uint8_t v___x_22_; 
lean_dec_ref(v_c_3_);
v___x_22_ = 1;
return v___x_22_;
}
default: 
{
uint8_t v___x_23_; 
lean_dec_ref(v_c_3_);
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
lean_dec_ref(v___x_232_);
v___x_234_ = 0;
v___x_235_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_231_, v_a_233_, v___x_234_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v_fvarId_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
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
lean_dec_ref(v___x_306_);
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
lean_dec_ref(v___x_319_);
v_fst_321_ = lean_ctor_get(v_a_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v_a_320_, 1);
lean_inc(v_snd_322_);
lean_dec(v_a_320_);
v___x_323_ = 0;
v___x_324_ = 0;
lean_inc(v_a_294_);
lean_inc_ref(v_a_293_);
lean_inc(v_a_292_);
lean_inc_ref(v_a_291_);
v___x_325_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_323_, v_value_297_, v_fst_321_, v___x_324_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
lean_inc(v_a_326_);
v___x_327_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_326_, v___x_324_, v_a_289_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v___x_327_);
v___x_328_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_329_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_snd_322_, v_a_326_, v___x_328_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_326_);
lean_dec(v_snd_322_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
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
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
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
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
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
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
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
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
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
lean_dec_ref(v___x_494_);
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
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
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
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
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
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
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
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
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
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_fvarId_549_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* v_declName_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_env_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = lean_st_ref_get(v___y_561_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_563_);
v___x_565_ = l_Lean_isImplicitReducibleCore(v_env_564_, v_declName_560_);
v___x_566_ = lean_box(v___x_565_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_569_, v___y_570_);
lean_dec(v___y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* v_declName_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_573_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* v_declName_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(v_declName_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec_ref(v___x_640_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
v___x_653_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_631_, v_a_622_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
v_sz_694_ = lean_array_size(v_a_693_);
v___x_695_ = ((size_t)0ULL);
lean_inc(v_a_693_);
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
lean_inc(v_a_622_);
lean_inc_ref(v_a_621_);
lean_inc(v_a_620_);
lean_inc_ref(v_a_619_);
v___x_701_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_684_, v___x_699_, v___x_700_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v_fvarId_703_; lean_object* v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_701_);
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
lean_inc(v_a_622_);
lean_inc_ref(v_a_621_);
lean_inc(v_a_620_);
lean_inc_ref(v_a_619_);
v___x_708_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v_a_693_, v___x_706_, v___x_707_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_fvarId_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_708_);
v_fvarId_710_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_fvarId_710_);
lean_inc(v_fvarId_629_);
v___x_711_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_629_, v_fvarId_710_, v_a_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec_ref(v_a_619_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v___x_711_);
v___x_712_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_letDecl_615_, v_a_617_, v_a_620_);
lean_dec(v_a_620_);
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
lean_dec(v_a_620_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
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
uint8_t v___x_24505__boxed_824_; size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v___x_24505__boxed_824_ = lean_unbox(v___x_820_);
v_sz_boxed_825_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_826_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24505__boxed_824_, v_sz_boxed_825_, v_i_boxed_826_, v_bs_823_);
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
lean_dec_ref(v___x_968_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v_as_985_, size_t v_i_986_, size_t v_stop_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_eq(v_i_986_, v_stop_987_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; uint8_t v___x_990_; lean_object* v___y_996_; lean_object* v___x_997_; 
v___x_989_ = lean_nat_dec_eq(v___x_983_, v___x_984_);
v___x_990_ = 1;
v___x_997_ = lean_array_uget_borrowed(v_as_985_, v_i_986_);
switch(lean_obj_tag(v___x_997_))
{
case 0:
{
lean_object* v_code_998_; 
v_code_998_ = lean_ctor_get(v___x_997_, 2);
lean_inc_ref(v_code_998_);
v___y_996_ = v_code_998_;
goto v___jp_995_;
}
case 1:
{
lean_object* v_code_999_; 
v_code_999_ = lean_ctor_get(v___x_997_, 1);
lean_inc_ref(v_code_999_);
v___y_996_ = v_code_999_;
goto v___jp_995_;
}
default: 
{
lean_object* v_code_1000_; 
v_code_1000_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_code_1000_);
v___y_996_ = v_code_1000_;
goto v___jp_995_;
}
}
v___jp_991_:
{
if (v___x_989_ == 0)
{
size_t v___x_992_; size_t v___x_993_; 
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_986_, v___x_992_);
v_i_986_ = v___x_993_;
goto _start;
}
else
{
return v___x_990_;
}
}
v___jp_995_:
{
if (lean_obj_tag(v___y_996_) == 6)
{
lean_dec_ref(v___y_996_);
goto v___jp_991_;
}
else
{
lean_dec_ref(v___y_996_);
if (v___x_989_ == 0)
{
return v___x_990_;
}
else
{
goto v___jp_991_;
}
}
}
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_as_1004_, lean_object* v_i_1005_, lean_object* v_stop_1006_){
_start:
{
size_t v_i_boxed_1007_; size_t v_stop_boxed_1008_; uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_i_boxed_1007_ = lean_unbox_usize(v_i_1005_);
lean_dec(v_i_1005_);
v_stop_boxed_1008_ = lean_unbox_usize(v_stop_1006_);
lean_dec(v_stop_1006_);
v_res_1009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___x_1002_, v___x_1003_, v_as_1004_, v_i_boxed_1007_, v_stop_boxed_1008_);
lean_dec_ref(v_as_1004_);
lean_dec(v___x_1003_);
lean_dec(v___x_1002_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t v_pu_1011_, uint8_t v_t_1012_, lean_object* v_i_1013_, lean_object* v_as_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_as_1014_);
v___x_1019_ = lean_nat_dec_lt(v_i_1013_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec(v_i_1013_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_as_1014_);
return v___x_1020_;
}
else
{
lean_object* v_a_1021_; lean_object* v_type_1022_; lean_object* v___x_1023_; lean_object* v_subst_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1021_ = lean_array_fget_borrowed(v_as_1014_, v_i_1013_);
v_type_1022_ = lean_ctor_get(v_a_1021_, 2);
v___x_1023_ = lean_st_ref_get(v___y_1015_);
v_subst_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_subst_1024_);
lean_dec(v___x_1023_);
lean_inc_ref(v_type_1022_);
v___x_1025_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1011_, v_subst_1024_, v_t_1012_, v_type_1022_);
lean_dec_ref(v_subst_1024_);
lean_inc(v_a_1021_);
v___x_1026_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_1011_, v_a_1021_, v___x_1025_, v___y_1016_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; size_t v___x_1028_; size_t v___x_1029_; uint8_t v___x_1030_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_ptr_addr(v_a_1021_);
v___x_1029_ = lean_ptr_addr(v_a_1027_);
v___x_1030_ = lean_usize_dec_eq(v___x_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_i_1013_, v___x_1031_);
v___x_1033_ = lean_array_fset(v_as_1014_, v_i_1013_, v_a_1027_);
lean_dec(v_i_1013_);
v_i_1013_ = v___x_1032_;
v_as_1014_ = v___x_1033_;
goto _start;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_a_1027_);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_add(v_i_1013_, v___x_1035_);
lean_dec(v_i_1013_);
v_i_1013_ = v___x_1036_;
goto _start;
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_as_1014_);
lean_dec(v_i_1013_);
v_a_1038_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1026_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1026_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* v_pu_1046_, lean_object* v_t_1047_, lean_object* v_i_1048_, lean_object* v_as_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_pu_boxed_1053_; uint8_t v_t_boxed_1054_; lean_object* v_res_1055_; 
v_pu_boxed_1053_ = lean_unbox(v_pu_1046_);
v_t_boxed_1054_ = lean_unbox(v_t_1047_);
v_res_1055_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_1053_, v_t_boxed_1054_, v_i_1048_, v_as_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t v_pu_1056_, uint8_t v_t_1057_, lean_object* v_ps_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_1056_, v_t_1057_, v___x_1067_, v_ps_1058_, v___y_1060_, v___y_1063_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* v_pu_1069_, lean_object* v_t_1070_, lean_object* v_ps_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_pu_boxed_1080_; uint8_t v_t_boxed_1081_; lean_object* v_res_1082_; 
v_pu_boxed_1080_ = lean_unbox(v_pu_1069_);
v_t_boxed_1081_ = lean_unbox(v_t_1070_);
v_res_1082_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v_pu_boxed_1080_, v_t_boxed_1081_, v_ps_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t v_pu_1083_, uint8_t v_t_1084_, lean_object* v_decl_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_type_1089_; lean_object* v_value_1090_; lean_object* v___x_1091_; lean_object* v_subst_1092_; lean_object* v___x_1093_; lean_object* v_subst_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_type_1089_ = lean_ctor_get(v_decl_1085_, 2);
v_value_1090_ = lean_ctor_get(v_decl_1085_, 3);
v___x_1091_ = lean_st_ref_get(v___y_1086_);
v_subst_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_subst_1092_);
lean_dec(v___x_1091_);
v___x_1093_ = lean_st_ref_get(v___y_1086_);
v_subst_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_subst_1094_);
lean_dec(v___x_1093_);
lean_inc_ref(v_type_1089_);
v___x_1095_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_1083_, v_subst_1092_, v_t_1084_, v_type_1089_);
lean_dec_ref(v_subst_1092_);
lean_inc(v_value_1090_);
v___x_1096_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v_pu_1083_, v_subst_1094_, v_value_1090_, v_t_1084_);
lean_dec_ref(v_subst_1094_);
v___x_1097_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v_pu_1083_, v_decl_1085_, v___x_1095_, v___x_1096_, v___y_1087_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* v_pu_1098_, lean_object* v_t_1099_, lean_object* v_decl_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_pu_boxed_1104_; uint8_t v_t_boxed_1105_; lean_object* v_res_1106_; 
v_pu_boxed_1104_ = lean_unbox(v_pu_1098_);
v_t_boxed_1105_ = lean_unbox(v_t_1099_);
v_res_1106_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_boxed_1104_, v_t_boxed_1105_, v_decl_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* v___y_1107_, lean_object* v___f_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v_fvarId_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
lean_inc(v_fvarId_1111_);
v___x_1117_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1111_, v___y_1107_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1117_);
v___x_1118_ = lean_apply_9(v___f_1108_, v_fvarId_1111_, v___y_1109_, v___y_1107_, v___y_1110_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
return v___x_1118_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v_fvarId_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___f_1108_);
lean_dec(v___y_1107_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* v___y_1127_, lean_object* v___f_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v_fvarId_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(v___y_1127_, v___f_1128_, v___y_1129_, v___y_1130_, v_fvarId_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_ks_1142_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1138_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v_x_1138_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_inc(v_ks_1142_);
lean_dec(v_x_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_get_size(v_ks_1142_);
v___x_1148_ = lean_nat_dec_lt(v_x_1139_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_x_1139_);
v___x_1149_ = lean_array_push(v_ks_1142_, v_x_1140_);
v___x_1150_ = lean_array_push(v_vs_1143_, v_x_1141_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1150_);
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v_k_x27_1154_; uint8_t v___x_1155_; 
v_k_x27_1154_ = lean_array_fget_borrowed(v_ks_1142_, v_x_1139_);
v___x_1155_ = lean_name_eq(v_x_1140_, v_k_x27_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1146_ == 0)
{
v___x_1157_ = v___x_1145_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_ks_1142_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_vs_1143_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_x_1139_, v___x_1158_);
lean_dec(v_x_1139_);
v_x_1138_ = v___x_1157_;
v_x_1139_ = v___x_1159_;
goto _start;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_array_fset(v_ks_1142_, v_x_1139_, v_x_1140_);
v___x_1163_ = lean_array_fset(v_vs_1143_, v_x_1139_, v_x_1141_);
lean_dec(v_x_1139_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1163_);
lean_ctor_set(v___x_1145_, 0, v___x_1162_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* v_n_1168_, lean_object* v_k_1169_, lean_object* v_v_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_1168_, v___x_1171_, v_k_1169_, v_v_1170_);
return v___x_1172_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1173_; uint64_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1723u);
v___x_1174_ = lean_uint64_of_nat(v___x_1173_);
return v___x_1174_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; 
v___x_1175_ = ((size_t)5ULL);
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = lean_usize_shift_left(v___x_1176_, v___x_1175_);
return v___x_1177_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1180_ = lean_usize_sub(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1182_, size_t v_x_1183_, size_t v_x_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 0)
{
lean_object* v_es_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v_j_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_es_1187_ = lean_ctor_get(v_x_1182_, 0);
v___x_1188_ = ((size_t)5ULL);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1);
v___x_1191_ = lean_usize_land(v_x_1183_, v___x_1190_);
v_j_1192_ = lean_usize_to_nat(v___x_1191_);
v___x_1193_ = lean_array_get_size(v_es_1187_);
v___x_1194_ = lean_nat_dec_lt(v_j_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec(v_j_1192_);
lean_dec(v_x_1186_);
lean_dec(v_x_1185_);
return v_x_1182_;
}
else
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1231_; 
lean_inc_ref(v_es_1187_);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_x_1182_, 0);
lean_dec(v_unused_1232_);
v___x_1196_ = v_x_1182_;
v_isShared_1197_ = v_isSharedCheck_1231_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v_x_1182_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1231_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_v_1198_; lean_object* v___x_1199_; lean_object* v_xs_x27_1200_; lean_object* v___y_1202_; 
v_v_1198_ = lean_array_fget(v_es_1187_, v_j_1192_);
v___x_1199_ = lean_box(0);
v_xs_x27_1200_ = lean_array_fset(v_es_1187_, v_j_1192_, v___x_1199_);
switch(lean_obj_tag(v_v_1198_))
{
case 0:
{
lean_object* v_key_1207_; lean_object* v_val_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1218_; 
v_key_1207_ = lean_ctor_get(v_v_1198_, 0);
v_val_1208_ = lean_ctor_get(v_v_1198_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_v_1198_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1210_ = v_v_1198_;
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_val_1208_);
lean_inc(v_key_1207_);
lean_dec(v_v_1198_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_name_eq(v_x_1185_, v_key_1207_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_del_object(v___x_1210_);
v___x_1213_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1207_, v_val_1208_, v_x_1185_, v_x_1186_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___y_1202_ = v___x_1214_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_val_1208_);
lean_dec(v_key_1207_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v_x_1186_);
lean_ctor_set(v___x_1210_, 0, v_x_1185_);
v___x_1216_ = v___x_1210_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_x_1185_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_x_1186_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v___y_1202_ = v___x_1216_;
goto v___jp_1201_;
}
}
}
}
case 1:
{
lean_object* v_node_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1229_; 
v_node_1219_ = lean_ctor_get(v_v_1198_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_v_1198_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1221_ = v_v_1198_;
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_node_1219_);
lean_dec(v_v_1198_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1223_ = lean_usize_shift_right(v_x_1183_, v___x_1188_);
v___x_1224_ = lean_usize_add(v_x_1184_, v___x_1189_);
v___x_1225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1219_, v___x_1223_, v___x_1224_, v_x_1185_, v_x_1186_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1225_);
v___x_1227_ = v___x_1221_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v___y_1202_ = v___x_1227_;
goto v___jp_1201_;
}
}
}
default: 
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_x_1185_);
lean_ctor_set(v___x_1230_, 1, v_x_1186_);
v___y_1202_ = v___x_1230_;
goto v___jp_1201_;
}
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_array_fset(v_xs_x27_1200_, v_j_1192_, v___y_1202_);
lean_dec(v_j_1192_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1203_);
v___x_1205_ = v___x_1196_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_object* v_ks_1233_; lean_object* v_vs_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1254_; 
v_ks_1233_ = lean_ctor_get(v_x_1182_, 0);
v_vs_1234_ = lean_ctor_get(v_x_1182_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1236_ = v_x_1182_;
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_vs_1234_);
lean_inc(v_ks_1233_);
lean_dec(v_x_1182_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_ks_1233_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_vs_1234_);
v___x_1239_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v_newNode_1240_; uint8_t v___y_1242_; size_t v___x_1248_; uint8_t v___x_1249_; 
v_newNode_1240_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1239_, v_x_1185_, v_x_1186_);
v___x_1248_ = ((size_t)7ULL);
v___x_1249_ = lean_usize_dec_le(v___x_1248_, v_x_1184_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1240_);
v___x_1251_ = lean_unsigned_to_nat(4u);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
lean_dec(v___x_1250_);
v___y_1242_ = v___x_1252_;
goto v___jp_1241_;
}
else
{
v___y_1242_ = v___x_1249_;
goto v___jp_1241_;
}
v___jp_1241_:
{
if (v___y_1242_ == 0)
{
lean_object* v_ks_1243_; lean_object* v_vs_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_ks_1243_ = lean_ctor_get(v_newNode_1240_, 0);
lean_inc_ref(v_ks_1243_);
v_vs_1244_ = lean_ctor_get(v_newNode_1240_, 1);
lean_inc_ref(v_vs_1244_);
lean_dec_ref(v_newNode_1240_);
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2);
v___x_1247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1184_, v_ks_1243_, v_vs_1244_, v___x_1245_, v___x_1246_);
lean_dec_ref(v_vs_1244_);
lean_dec_ref(v_ks_1243_);
return v___x_1247_;
}
else
{
return v_newNode_1240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1255_, lean_object* v_keys_1256_, lean_object* v_vals_1257_, lean_object* v_i_1258_, lean_object* v_entries_1259_){
_start:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_array_get_size(v_keys_1256_);
v___x_1261_ = lean_nat_dec_lt(v_i_1258_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v_i_1258_);
return v_entries_1259_;
}
else
{
lean_object* v_k_1262_; lean_object* v_v_1263_; uint64_t v___y_1265_; 
v_k_1262_ = lean_array_fget_borrowed(v_keys_1256_, v_i_1258_);
v_v_1263_ = lean_array_fget_borrowed(v_vals_1257_, v_i_1258_);
if (lean_obj_tag(v_k_1262_) == 0)
{
uint64_t v___x_1276_; 
v___x_1276_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1265_ = v___x_1276_;
goto v___jp_1264_;
}
else
{
uint64_t v_hash_1277_; 
v_hash_1277_ = lean_ctor_get_uint64(v_k_1262_, sizeof(void*)*2);
v___y_1265_ = v_hash_1277_;
goto v___jp_1264_;
}
v___jp_1264_:
{
size_t v_h_1266_; size_t v___x_1267_; lean_object* v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v_h_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_h_1266_ = lean_uint64_to_usize(v___y_1265_);
v___x_1267_ = ((size_t)5ULL);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_sub(v_depth_1255_, v___x_1269_);
v___x_1271_ = lean_usize_mul(v___x_1267_, v___x_1270_);
v_h_1272_ = lean_usize_shift_right(v_h_1266_, v___x_1271_);
v___x_1273_ = lean_nat_add(v_i_1258_, v___x_1268_);
lean_dec(v_i_1258_);
lean_inc(v_v_1263_);
lean_inc(v_k_1262_);
v___x_1274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1259_, v_h_1272_, v_depth_1255_, v_k_1262_, v_v_1263_);
v_i_1258_ = v___x_1273_;
v_entries_1259_ = v___x_1274_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_i_1281_, lean_object* v_entries_1282_){
_start:
{
size_t v_depth_boxed_1283_; lean_object* v_res_1284_; 
v_depth_boxed_1283_ = lean_unbox_usize(v_depth_1278_);
lean_dec(v_depth_1278_);
v_res_1284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1283_, v_keys_1279_, v_vals_1280_, v_i_1281_, v_entries_1282_);
lean_dec_ref(v_vals_1280_);
lean_dec_ref(v_keys_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
size_t v_x_45260__boxed_1290_; size_t v_x_45261__boxed_1291_; lean_object* v_res_1292_; 
v_x_45260__boxed_1290_ = lean_unbox_usize(v_x_1286_);
lean_dec(v_x_1286_);
v_x_45261__boxed_1291_ = lean_unbox_usize(v_x_1287_);
lean_dec(v_x_1287_);
v_res_1292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1285_, v_x_45260__boxed_1290_, v_x_45261__boxed_1291_, v_x_1288_, v_x_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
uint64_t v___y_1297_; 
if (lean_obj_tag(v_x_1294_) == 0)
{
uint64_t v___x_1301_; 
v___x_1301_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1297_ = v___x_1301_;
goto v___jp_1296_;
}
else
{
uint64_t v_hash_1302_; 
v_hash_1302_ = lean_ctor_get_uint64(v_x_1294_, sizeof(void*)*2);
v___y_1297_ = v_hash_1302_;
goto v___jp_1296_;
}
v___jp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_uint64_to_usize(v___y_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1293_, v___x_1298_, v___x_1299_, v_x_1294_, v_x_1295_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1303_, lean_object* v_b_1304_){
_start:
{
lean_object* v_array_1305_; lean_object* v_start_1306_; lean_object* v_stop_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1320_; 
v_array_1305_ = lean_ctor_get(v_a_1303_, 0);
v_start_1306_ = lean_ctor_get(v_a_1303_, 1);
v_stop_1307_ = lean_ctor_get(v_a_1303_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1303_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1309_ = v_a_1303_;
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_stop_1307_);
lean_inc(v_start_1306_);
lean_inc(v_array_1305_);
lean_dec(v_a_1303_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_lt(v_start_1306_, v_stop_1307_);
if (v___x_1311_ == 0)
{
lean_del_object(v___x_1309_);
lean_dec(v_stop_1307_);
lean_dec(v_start_1306_);
lean_dec_ref(v_array_1305_);
return v_b_1304_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_add(v_start_1306_, v___x_1312_);
lean_inc_ref(v_array_1305_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___x_1313_);
v___x_1315_ = v___x_1309_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_array_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_stop_1307_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_array_fget(v_array_1305_, v_start_1306_);
lean_dec(v_start_1306_);
lean_dec_ref(v_array_1305_);
v___x_1317_ = lean_array_push(v_b_1304_, v___x_1316_);
v_a_1303_ = v___x_1315_;
v_b_1304_ = v___x_1317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1321_, size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_b_1324_);
return v___x_1328_;
}
else
{
lean_object* v_array_1329_; lean_object* v_start_1330_; lean_object* v_stop_1331_; uint8_t v___x_1332_; 
v_array_1329_ = lean_ctor_get(v_b_1324_, 0);
v_start_1330_ = lean_ctor_get(v_b_1324_, 1);
v_stop_1331_ = lean_ctor_get(v_b_1324_, 2);
v___x_1332_ = lean_nat_dec_lt(v_start_1330_, v_stop_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_b_1324_);
return v___x_1333_;
}
else
{
lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1366_; 
lean_inc(v_stop_1331_);
lean_inc(v_start_1330_);
lean_inc_ref(v_array_1329_);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_b_1324_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v_b_1324_, 2);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_b_1324_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_b_1324_, 0);
lean_dec(v_unused_1369_);
v___x_1335_ = v_b_1324_;
v_isShared_1336_ = v_isSharedCheck_1366_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v_b_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1366_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v_fvarId_1339_; lean_object* v_subst_1340_; lean_object* v_used_1341_; lean_object* v_binderRenaming_1342_; lean_object* v_funDeclInfoMap_1343_; uint8_t v_simplified_1344_; lean_object* v_visited_1345_; lean_object* v_inline_1346_; lean_object* v_inlineLocal_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1365_; 
v___x_1337_ = lean_st_ref_take(v___y_1325_);
v_a_1338_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
v_fvarId_1339_ = lean_ctor_get(v_a_1338_, 0);
v_subst_1340_ = lean_ctor_get(v___x_1337_, 0);
v_used_1341_ = lean_ctor_get(v___x_1337_, 1);
v_binderRenaming_1342_ = lean_ctor_get(v___x_1337_, 2);
v_funDeclInfoMap_1343_ = lean_ctor_get(v___x_1337_, 3);
v_simplified_1344_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*7);
v_visited_1345_ = lean_ctor_get(v___x_1337_, 4);
v_inline_1346_ = lean_ctor_get(v___x_1337_, 5);
v_inlineLocal_1347_ = lean_ctor_get(v___x_1337_, 6);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_inlineLocal_1347_);
lean_inc(v_inline_1346_);
lean_inc(v_visited_1345_);
lean_inc(v_funDeclInfoMap_1343_);
lean_inc(v_binderRenaming_1342_);
lean_inc(v_used_1341_);
lean_inc(v_subst_1340_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_array_fget_borrowed(v_array_1329_, v_start_1330_);
lean_inc(v___x_1351_);
lean_inc(v_fvarId_1339_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1340_, v_fvarId_1339_, v___x_1351_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_used_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_binderRenaming_1342_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_funDeclInfoMap_1343_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_visited_1345_);
lean_ctor_set(v_reuseFailAlloc_1364_, 5, v_inline_1346_);
lean_ctor_set(v_reuseFailAlloc_1364_, 6, v_inlineLocal_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*7, v_simplified_1344_);
v___x_1354_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1355_ = lean_st_ref_set(v___y_1325_, v___x_1354_);
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v_start_1330_, v___x_1356_);
lean_dec(v_start_1330_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v___x_1357_);
v___x_1359_ = v___x_1335_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_array_1329_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_stop_1331_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
size_t v___x_1360_; size_t v___x_1361_; 
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1323_, v___x_1360_);
v_i_1323_ = v___x_1361_;
v_b_1324_ = v___x_1359_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1370_, lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_b_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1370_, v_sz_boxed_1376_, v_i_boxed_1377_, v_b_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v_as_1370_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1379_, size_t v_i_1380_, size_t v_stop_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_eq(v_i_1380_, v_stop_1381_);
if (v___x_1385_ == 0)
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = 0;
v___x_1387_ = lean_array_uget_borrowed(v_as_1379_, v_i_1380_);
v___x_1388_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1386_, v___x_1387_, v___y_1383_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; size_t v___x_1390_; size_t v___x_1391_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_add(v_i_1380_, v___x_1390_);
v_i_1380_ = v___x_1391_;
v_b_1382_ = v_a_1389_;
goto _start;
}
else
{
return v___x_1388_;
}
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1382_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1394_, lean_object* v_i_1395_, lean_object* v_stop_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
size_t v_i_boxed_1400_; size_t v_stop_boxed_1401_; lean_object* v_res_1402_; 
v_i_boxed_1400_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_stop_boxed_1401_ = lean_unbox_usize(v_stop_1396_);
lean_dec(v_stop_1396_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1394_, v_i_boxed_1400_, v_stop_boxed_1401_, v_b_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v_as_1394_);
return v_res_1402_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = 0;
v___x_1404_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1407_ = lean_panic_fn(v___x_1406_, v_msg_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1408_, size_t v_i_1409_, size_t v_stop_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_usize_dec_eq(v_i_1409_, v_stop_1410_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v_type_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_array_uget_borrowed(v_as_1408_, v_i_1409_);
v_type_1415_ = lean_ctor_get(v___x_1414_, 2);
v___x_1416_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1415_, v___y_1411_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1428_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1428_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1428_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_unbox(v_a_1417_);
if (v___x_1421_ == 0)
{
size_t v___x_1422_; size_t v___x_1423_; 
lean_del_object(v___x_1419_);
lean_dec(v_a_1417_);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1409_, v___x_1422_);
v_i_1409_ = v___x_1423_;
goto _start;
}
else
{
lean_object* v___x_1426_; 
if (v_isShared_1420_ == 0)
{
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1417_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
return v___x_1416_;
}
}
else
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = 0;
v___x_1430_ = lean_box(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1432_, lean_object* v_i_1433_, lean_object* v_stop_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
size_t v_i_boxed_1437_; size_t v_stop_boxed_1438_; lean_object* v_res_1439_; 
v_i_boxed_1437_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_stop_boxed_1438_ = lean_unbox_usize(v_stop_1434_);
lean_dec(v_stop_1434_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1432_, v_i_boxed_1437_, v_stop_boxed_1438_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v_as_1432_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1440_, size_t v_i_1441_, size_t v_stop_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_eq(v_i_1441_, v_stop_1442_);
if (v___x_1446_ == 0)
{
uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = 0;
v___x_1448_ = lean_array_uget_borrowed(v_as_1440_, v_i_1441_);
v___x_1449_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1447_, v___x_1448_, v___y_1444_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; size_t v___x_1451_; size_t v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1441_, v___x_1451_);
v_i_1441_ = v___x_1452_;
v_b_1443_ = v_a_1450_;
goto _start;
}
else
{
return v___x_1449_;
}
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1443_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1455_, lean_object* v_i_1456_, lean_object* v_stop_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
size_t v_i_boxed_1461_; size_t v_stop_boxed_1462_; lean_object* v_res_1463_; 
v_i_boxed_1461_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_stop_boxed_1462_ = lean_unbox_usize(v_stop_1457_);
lean_dec(v_stop_1457_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1455_, v_i_boxed_1461_, v_stop_boxed_1462_, v_b_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1464_, size_t v_i_1465_, size_t v_stop_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_a_1474_; lean_object* v___y_1479_; uint8_t v___x_1481_; 
v___x_1481_ = lean_usize_dec_eq(v_i_1465_, v_stop_1466_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = lean_array_uget_borrowed(v_as_1464_, v_i_1465_);
v___x_1484_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1483_);
v___x_1485_ = lean_array_get_size(v___x_1484_);
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_nat_dec_lt(v___x_1482_, v___x_1485_);
if (v___x_1487_ == 0)
{
lean_dec_ref(v___x_1484_);
v_a_1474_ = v___x_1486_;
goto v___jp_1473_;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_le(v___x_1485_, v___x_1485_);
if (v___x_1488_ == 0)
{
if (v___x_1487_ == 0)
{
lean_dec_ref(v___x_1484_);
v_a_1474_ = v___x_1486_;
goto v___jp_1473_;
}
else
{
size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = lean_usize_of_nat(v___x_1485_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1484_, v___x_1489_, v___x_1490_, v___x_1486_, v___y_1469_);
lean_dec_ref(v___x_1484_);
v___y_1479_ = v___x_1491_;
goto v___jp_1478_;
}
}
else
{
size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = lean_usize_of_nat(v___x_1485_);
v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1484_, v___x_1492_, v___x_1493_, v___x_1486_, v___y_1469_);
lean_dec_ref(v___x_1484_);
v___y_1479_ = v___x_1494_;
goto v___jp_1478_;
}
}
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1467_);
return v___x_1495_;
}
v___jp_1473_:
{
size_t v___x_1475_; size_t v___x_1476_; 
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1465_, v___x_1475_);
v_i_1465_ = v___x_1476_;
v_b_1467_ = v_a_1474_;
goto _start;
}
v___jp_1478_:
{
if (lean_obj_tag(v___y_1479_) == 0)
{
lean_object* v_a_1480_; 
v_a_1480_ = lean_ctor_get(v___y_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___y_1479_);
v_a_1474_ = v_a_1480_;
goto v___jp_1473_;
}
else
{
return v___y_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1496_, lean_object* v_i_1497_, lean_object* v_stop_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
size_t v_i_boxed_1505_; size_t v_stop_boxed_1506_; lean_object* v_res_1507_; 
v_i_boxed_1505_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_stop_boxed_1506_ = lean_unbox_usize(v_stop_1498_);
lean_dec(v_stop_1498_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1496_, v_i_boxed_1505_, v_stop_boxed_1506_, v_b_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v_as_1496_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1508_, size_t v_i_1509_, size_t v_stop_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_eq(v_i_1509_, v_stop_1510_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v_fvarId_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_array_uget_borrowed(v_as_1508_, v_i_1509_);
v_fvarId_1515_ = lean_ctor_get(v___x_1514_, 0);
v___x_1516_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1515_, v___y_1511_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1528_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_unbox(v_a_1517_);
if (v___x_1521_ == 0)
{
size_t v___x_1522_; size_t v___x_1523_; 
lean_del_object(v___x_1519_);
lean_dec(v_a_1517_);
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1509_, v___x_1522_);
v_i_1509_ = v___x_1523_;
goto _start;
}
else
{
lean_object* v___x_1526_; 
if (v_isShared_1520_ == 0)
{
v___x_1526_ = v___x_1519_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1517_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
return v___x_1516_;
}
}
else
{
uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = 0;
v___x_1530_ = lean_box(v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1532_, lean_object* v_i_1533_, lean_object* v_stop_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
size_t v_i_boxed_1537_; size_t v_stop_boxed_1538_; lean_object* v_res_1539_; 
v_i_boxed_1537_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_stop_boxed_1538_ = lean_unbox_usize(v_stop_1534_);
lean_dec(v_stop_1534_);
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1532_, v_i_boxed_1537_, v_stop_boxed_1538_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v_as_1532_);
return v_res_1539_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1543_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1544_ = lean_unsigned_to_nat(9u);
v___x_1545_ = lean_unsigned_to_nat(635u);
v___x_1546_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1547_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1547_, v___x_1546_, v___x_1545_, v___x_1544_, v___x_1543_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v_fvarId_1554_, lean_object* v_k_1555_, lean_object* v_args_1556_, uint8_t v___x_1557_, lean_object* v___x_1558_, lean_object* v_result_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_lower_1569_; lean_object* v_upper_1570_; uint8_t v___x_1597_; 
v___x_1597_ = lean_nat_dec_lt(v___x_1552_, v___x_1553_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v___x_1558_);
lean_dec_ref(v_args_1556_);
lean_dec(v___x_1553_);
lean_dec(v___x_1552_);
v___x_1598_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1554_, v_result_1559_, v___y_1561_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref(v___x_1598_);
v___x_1599_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1555_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1599_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_k_1555_);
v_a_1600_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1598_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_nat_dec_le(v___x_1552_, v___x_1558_);
if (v___x_1608_ == 0)
{
lean_dec(v___x_1558_);
v_lower_1569_ = v___x_1552_;
v_upper_1570_ = v___x_1553_;
goto v___jp_1568_;
}
else
{
lean_dec(v___x_1552_);
v_lower_1569_ = v___x_1558_;
v_upper_1570_ = v___x_1553_;
goto v___jp_1568_;
}
}
v___jp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = l_Array_toSubarray___redArg(v_args_1556_, v_lower_1569_, v_upper_1570_);
v___x_1572_ = l_Subarray_copy___redArg(v___x_1571_);
v___x_1573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_result_1559_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(v___y_1566_);
lean_inc_ref(v___y_1565_);
lean_inc(v___y_1564_);
lean_inc_ref(v___y_1563_);
v___x_1575_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1557_, v___x_1573_, v___x_1574_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_fvarId_1577_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
v_fvarId_1577_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_fvarId_1577_);
v___x_1578_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1554_, v_fvarId_1577_, v___y_1561_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v___x_1578_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_a_1576_);
lean_ctor_set(v___x_1579_, 1, v_k_1555_);
v___x_1580_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1579_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1580_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1576_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_k_1555_);
v_a_1581_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1578_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1578_);
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
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_k_1555_);
lean_dec(v_fvarId_1554_);
v_a_1589_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1575_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1575_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_fvarId_1611_, lean_object* v_k_1612_, lean_object* v_args_1613_, lean_object* v___x_1614_, lean_object* v___x_1615_, lean_object* v_result_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
uint8_t v___x_45797__boxed_1625_; lean_object* v_res_1626_; 
v___x_45797__boxed_1625_ = lean_unbox(v___x_1614_);
v_res_1626_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1609_, v___x_1610_, v_fvarId_1611_, v_k_1612_, v_args_1613_, v___x_45797__boxed_1625_, v___x_1615_, v_result_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1627_, lean_object* v_k_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_fvarId_1637_; lean_object* v_value_1638_; lean_object* v___x_1639_; 
v_fvarId_1637_ = lean_ctor_get(v_letDecl_1627_, 0);
lean_inc(v_fvarId_1637_);
v_value_1638_ = lean_ctor_get(v_letDecl_1627_, 3);
lean_inc(v_value_1638_);
lean_dec_ref(v_letDecl_1627_);
lean_inc(v_a_1635_);
lean_inc_ref(v_a_1634_);
lean_inc(v_a_1633_);
lean_inc_ref(v_a_1632_);
lean_inc_ref(v_a_1631_);
lean_inc(v_a_1630_);
lean_inc_ref(v_a_1629_);
lean_inc(v_value_1638_);
v___x_1639_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1638_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1968_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1968_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1968_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
if (lean_obj_tag(v_a_1640_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1642_);
v_val_1644_ = lean_ctor_get(v_a_1640_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1646_ = v_a_1640_;
v_isShared_1647_ = v_isSharedCheck_1963_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v_a_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1963_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_params_1648_; lean_object* v_value_1649_; lean_object* v_fType_1650_; lean_object* v_args_1651_; uint8_t v_recursive_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; 
v_params_1648_ = lean_ctor_get(v_val_1644_, 0);
v_value_1649_ = lean_ctor_get(v_val_1644_, 1);
v_fType_1650_ = lean_ctor_get(v_val_1644_, 2);
v_args_1651_ = lean_ctor_get(v_val_1644_, 3);
v_recursive_1652_ = lean_ctor_get_uint8(v_val_1644_, sizeof(void*)*4 + 2);
v___x_1653_ = lean_array_get_size(v_args_1651_);
v___x_1654_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1644_);
v___x_1655_ = lean_nat_dec_lt(v___x_1653_, v___x_1654_);
if (lean_obj_tag(v_value_1638_) == 3)
{
lean_object* v_declName_1939_; lean_object* v___x_1940_; 
v_declName_1939_ = lean_ctor_get(v_value_1638_, 0);
lean_inc(v_declName_1939_);
lean_dec_ref(v_value_1638_);
lean_inc_ref(v_a_1629_);
lean_inc(v_declName_1939_);
v___x_1940_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1652_, v_declName_1939_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_declName_1942_; lean_object* v_config_1943_; lean_object* v_inlineStack_1944_; lean_object* v_inlineStackOccs_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1954_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v___x_1940_);
v_declName_1942_ = lean_ctor_get(v_a_1629_, 0);
v_config_1943_ = lean_ctor_get(v_a_1629_, 1);
v_inlineStack_1944_ = lean_ctor_get(v_a_1629_, 2);
v_inlineStackOccs_1945_ = lean_ctor_get(v_a_1629_, 3);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1947_ = v_a_1629_;
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_inlineStackOccs_1945_);
lean_inc(v_inlineStack_1944_);
lean_inc(v_config_1943_);
lean_inc(v_declName_1942_);
lean_dec(v_a_1629_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_inc(v_declName_1939_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_declName_1939_);
lean_ctor_set(v___x_1949_, 1, v_inlineStack_1944_);
v___x_1950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1945_, v_declName_1939_, v_a_1941_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 3, v___x_1950_);
lean_ctor_set(v___x_1947_, 2, v___x_1949_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_declName_1942_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_config_1943_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
v___y_1838_ = v___x_1952_;
v___y_1839_ = v_a_1630_;
v___y_1840_ = v_a_1631_;
v___y_1841_ = v_a_1632_;
v___y_1842_ = v_a_1633_;
v___y_1843_ = v_a_1634_;
v___y_1844_ = v_a_1635_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_declName_1939_);
lean_dec(v___x_1654_);
lean_del_object(v___x_1646_);
lean_dec(v_val_1644_);
lean_dec(v_fvarId_1637_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec_ref(v_k_1628_);
v_a_1955_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1940_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1940_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_dec(v_value_1638_);
v___y_1838_ = v_a_1629_;
v___y_1839_ = v_a_1630_;
v___y_1840_ = v_a_1631_;
v___y_1841_ = v_a_1632_;
v___y_1842_ = v_a_1633_;
v___y_1843_ = v_a_1634_;
v___y_1844_ = v_a_1635_;
goto v___jp_1837_;
}
v___jp_1656_:
{
lean_object* v___x_1670_; 
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1663_);
v___x_1670_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1658_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1667_);
if (lean_obj_tag(v___x_1672_) == 0)
{
uint8_t v___x_1673_; 
lean_dec_ref(v___x_1672_);
lean_inc(v_a_1671_);
v___x_1673_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1671_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec_ref(v___y_1657_);
v___x_1674_ = lean_mk_empty_array_with_capacity(v___y_1665_);
lean_dec(v___y_1665_);
lean_inc_ref(v___x_1674_);
v___x_1675_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1660_, v___x_1674_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
v___x_1676_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1661_, v_fType_1650_, v___x_1675_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
lean_inc(v_a_1677_);
v___x_1678_ = l_Lean_Expr_headBeta(v_a_1677_);
v___x_1679_ = l_Lean_Expr_isForall(v___x_1678_);
lean_dec_ref(v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref(v___x_1674_);
v___x_1680_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1661_, v_a_1677_, v___x_1655_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_fvarId_1682_; lean_object* v___x_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v_fvarId_1682_ = lean_ctor_get(v_a_1681_, 0);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
lean_inc(v_fvarId_1682_);
v___x_1683_ = lean_apply_9(v___y_1659_, v_fvarId_1682_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_, lean_box(0));
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_mk_empty_array_with_capacity(v___x_1685_);
v___x_1687_ = lean_array_push(v___x_1686_, v_a_1681_);
v___x_1688_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
v___x_1689_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1661_, v___x_1687_, v_a_1684_, v___x_1688_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
lean_inc(v_a_1690_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1691_, 0, v_a_1690_);
lean_closure_set(v___f_1691_, 1, v___x_1685_);
v___x_1692_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1661_, v_a_1671_, v___f_1691_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1704_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1704_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1690_);
lean_ctor_set(v___x_1697_, 1, v_a_1693_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1697_);
v___x_1699_ = v___x_1646_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1699_);
v___x_1701_ = v___x_1695_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_a_1690_);
lean_del_object(v___x_1646_);
v_a_1705_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1692_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1692_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_a_1671_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1662_);
lean_del_object(v___x_1646_);
v_a_1713_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1689_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1689_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1681_);
lean_dec(v_a_1671_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1662_);
lean_del_object(v___x_1646_);
v_a_1721_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1683_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1683_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1671_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1659_);
lean_del_object(v___x_1646_);
v_a_1729_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1680_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1680_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_a_1677_);
v___x_1737_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
v___x_1738_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1674_, v_a_1671_, v___x_1737_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
v___x_1740_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1739_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_fvarId_1742_; lean_object* v___x_1743_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v_fvarId_1742_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1662_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1663_);
lean_inc(v_fvarId_1742_);
v___x_1743_ = lean_apply_9(v___y_1659_, v_fvarId_1742_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_, lean_box(0));
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_a_1741_);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_array_push(v___x_1747_, v___x_1745_);
v___x_1749_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1748_, v_a_1744_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___x_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1760_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_a_1750_);
v___x_1755_ = v___x_1646_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_del_object(v___x_1646_);
v_a_1761_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1749_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1749_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1741_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_del_object(v___x_1646_);
v_a_1769_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1743_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1743_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1659_);
lean_del_object(v___x_1646_);
v_a_1777_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1740_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1740_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1659_);
lean_del_object(v___x_1646_);
v_a_1785_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1738_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1738_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___x_1674_);
lean_dec(v_a_1671_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1659_);
lean_del_object(v___x_1646_);
v_a_1793_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1676_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1676_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
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
lean_object* v___x_1801_; 
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_fType_1650_);
v___x_1801_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1661_, v_a_1671_, v___y_1657_, v___y_1662_, v___y_1668_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_a_1802_);
v___x_1807_ = v___x_1646_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1646_);
v_a_1813_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1801_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1801_);
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
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_a_1671_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_fType_1650_);
lean_del_object(v___x_1646_);
v_a_1821_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1672_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1672_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_fType_1650_);
lean_del_object(v___x_1646_);
v_a_1829_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1670_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1670_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
v___jp_1837_:
{
if (v___x_1655_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_inc_ref(v_args_1651_);
lean_inc_ref(v_fType_1650_);
lean_inc_ref(v_value_1649_);
lean_inc_ref(v_params_1648_);
lean_dec(v_val_1644_);
v___x_1845_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1654_);
lean_inc_ref(v_args_1651_);
v___x_1846_ = l_Array_toSubarray___redArg(v_args_1651_, v___x_1845_, v___x_1654_);
lean_inc_ref(v___x_1846_);
v___x_1847_ = l_Subarray_copy___redArg(v___x_1846_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
v___x_1848_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1648_, v_value_1649_, v___x_1847_, v___x_1655_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec_ref(v_params_1648_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; uint8_t v___x_1854_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = 0;
v___x_1851_ = lean_box(v___x_1850_);
lean_inc_ref(v_k_1628_);
lean_inc(v_fvarId_1637_);
lean_inc(v___x_1654_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1852_, 0, v___x_1654_);
lean_closure_set(v___f_1852_, 1, v___x_1653_);
lean_closure_set(v___f_1852_, 2, v_fvarId_1637_);
lean_closure_set(v___f_1852_, 3, v_k_1628_);
lean_closure_set(v___f_1852_, 4, v_args_1651_);
lean_closure_set(v___f_1852_, 5, v___x_1851_);
lean_closure_set(v___f_1852_, 6, v___x_1845_);
lean_inc_ref(v___y_1840_);
lean_inc_ref(v___y_1838_);
lean_inc_ref(v___f_1852_);
lean_inc(v___y_1839_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1853_, 0, v___y_1839_);
lean_closure_set(v___f_1853_, 1, v___f_1852_);
lean_closure_set(v___f_1853_, 2, v___y_1838_);
lean_closure_set(v___f_1853_, 3, v___y_1840_);
v___x_1854_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1628_, v_fvarId_1637_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
if (v___x_1854_ == 0)
{
lean_dec(v___x_1654_);
v___y_1657_ = v___f_1853_;
v___y_1658_ = v_a_1849_;
v___y_1659_ = v___f_1852_;
v___y_1660_ = v___x_1846_;
v___y_1661_ = v___x_1850_;
v___y_1662_ = v___y_1841_;
v___y_1663_ = v___y_1838_;
v___y_1664_ = v___y_1844_;
v___y_1665_ = v___x_1845_;
v___y_1666_ = v___y_1840_;
v___y_1667_ = v___y_1839_;
v___y_1668_ = v___y_1842_;
v___y_1669_ = v___y_1843_;
goto v___jp_1656_;
}
else
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_eq(v___x_1653_, v___x_1654_);
lean_dec(v___x_1654_);
if (v___x_1855_ == 0)
{
v___y_1657_ = v___f_1853_;
v___y_1658_ = v_a_1849_;
v___y_1659_ = v___f_1852_;
v___y_1660_ = v___x_1846_;
v___y_1661_ = v___x_1850_;
v___y_1662_ = v___y_1841_;
v___y_1663_ = v___y_1838_;
v___y_1664_ = v___y_1844_;
v___y_1665_ = v___x_1845_;
v___y_1666_ = v___y_1840_;
v___y_1667_ = v___y_1839_;
v___y_1668_ = v___y_1842_;
v___y_1669_ = v___y_1843_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___f_1853_);
lean_dec_ref(v___f_1852_);
lean_dec_ref(v___x_1846_);
lean_dec_ref(v_fType_1650_);
lean_del_object(v___x_1646_);
v___x_1856_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1839_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v___x_1856_);
v___x_1857_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1849_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_a_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1857_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1857_);
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
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1849_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1856_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1856_);
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
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v___x_1846_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___x_1654_);
lean_dec_ref(v_args_1651_);
lean_dec_ref(v_fType_1650_);
lean_del_object(v___x_1646_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1883_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1848_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1848_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v___x_1891_; 
lean_dec(v___x_1654_);
lean_del_object(v___x_1646_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
v___x_1891_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1644_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v_fvarId_1893_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v_fvarId_1893_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_fvarId_1893_);
v___x_1894_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1637_, v_fvarId_1893_, v___y_1839_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v___x_1894_);
v___x_1895_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1839_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v___x_1895_);
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1892_);
lean_ctor_set(v___x_1896_, 1, v_k_1628_);
v___x_1897_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1896_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1897_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1897_);
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
lean_dec(v_a_1892_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_k_1628_);
v_a_1915_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1895_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1895_);
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
lean_dec(v_a_1892_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_k_1628_);
v_a_1923_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1894_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1894_);
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
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1931_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1891_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1891_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_dec(v_a_1640_);
lean_dec(v_value_1638_);
lean_dec(v_fvarId_1637_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec_ref(v_k_1628_);
v___x_1964_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1964_);
v___x_1966_ = v___x_1642_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_value_1638_);
lean_dec(v_fvarId_1637_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec_ref(v_k_1628_);
v_a_1969_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1639_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1639_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
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
lean_dec_ref(v___x_1997_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec_ref(v___x_2034_);
v___x_2035_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1981_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref(v___x_2035_);
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
lean_dec_ref(v_fst_2027_);
v_val_2038_ = lean_ctor_get(v_val_2004_, 0);
lean_inc_ref(v_val_2038_);
v_args_2039_ = lean_ctor_get(v_val_2004_, 1);
lean_inc_ref(v_args_2039_);
lean_dec_ref(v_val_2004_);
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
lean_dec_ref(v___x_2046_);
lean_inc(v_a_1984_);
v___x_2047_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2037_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1995_, v_params_2036_, v_a_1984_);
lean_dec(v_a_1984_);
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
lean_dec(v_a_1984_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec_ref(v_fst_2027_);
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
lean_inc(v_a_1986_);
lean_inc_ref(v_a_1985_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
v___x_2124_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1995_, v___x_2122_, v___x_2123_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_fvarId_2128_; lean_object* v_fvarId_2129_; lean_object* v___x_2130_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
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
lean_dec_ref(v___x_2130_);
lean_inc(v_a_1984_);
v___x_2131_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2090_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1995_, v_params_2089_, v_a_1984_);
lean_dec(v_a_1984_);
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
lean_dec(v_a_1984_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec_ref(v_fst_2027_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec_ref(v_cases_1979_);
goto v___jp_1988_;
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_dec(v_a_2000_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
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
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec_ref(v_cases_1979_);
v___x_2238_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1995_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v_i_2259_, lean_object* v_as_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_array_get_size(v_as_2260_);
v___x_2270_ = lean_nat_dec_lt(v_i_2259_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_as_2260_);
return v___x_2271_;
}
else
{
lean_object* v_a_2272_; lean_object* v_a_2274_; 
v_a_2272_ = lean_array_fget_borrowed(v_as_2260_, v_i_2259_);
if (lean_obj_tag(v_a_2272_) == 0)
{
lean_object* v_ctorName_2285_; lean_object* v_params_2286_; lean_object* v_code_2287_; uint8_t v___x_2288_; uint8_t v___y_2290_; uint8_t v___x_2342_; uint8_t v___y_2344_; uint8_t v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_ctorName_2285_ = lean_ctor_get(v_a_2272_, 0);
v_params_2286_ = lean_ctor_get(v_a_2272_, 1);
v_code_2287_ = lean_ctor_get(v_a_2272_, 2);
v___x_2288_ = 0;
v___x_2342_ = lean_nat_dec_eq(v___x_2257_, v___x_2258_);
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_array_get_size(v_params_2286_);
v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
if (v___x_2349_ == 0)
{
v_a_2346_ = v___x_2342_;
goto v___jp_2345_;
}
else
{
if (v___x_2349_ == 0)
{
v_a_2346_ = v___x_2342_;
goto v___jp_2345_;
}
else
{
size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = lean_usize_of_nat(v___x_2348_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2286_, v___x_2350_, v___x_2351_, v___y_2267_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; uint8_t v___x_2354_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
v_a_2346_ = v___x_2354_;
goto v___jp_2345_;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2355_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2352_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2352_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
lean_object* v___x_2291_; 
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc_ref(v_params_2286_);
lean_inc(v_ctorName_2285_);
lean_inc(v_fvarId_2256_);
v___x_2291_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2256_, v_ctorName_2285_, v_params_2286_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc_ref(v_code_2287_);
v___x_2293_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2287_, v___y_2261_, v___y_2262_, v_a_2292_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
lean_inc_ref(v_a_2272_);
v___x_2295_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2272_, v_a_2294_);
v_a_2274_ = v___x_2295_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2296_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2293_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2293_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2304_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2291_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2291_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v___x_2312_; 
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v_code_2287_);
v___x_2312_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2288_, v_code_2287_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2288_, v_code_2287_, v___y_2265_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v___x_2315_; 
lean_dec_ref(v___x_2314_);
v___x_2315_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2262_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec_ref(v___x_2315_);
v___x_2316_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_a_2313_);
lean_inc_ref(v_a_2272_);
v___x_2317_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2272_, v___x_2316_);
v_a_2274_ = v___x_2317_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2313_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2318_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2315_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2315_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_a_2313_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2326_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2314_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2314_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2334_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2312_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2312_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
v___jp_2343_:
{
if (v___x_2342_ == 0)
{
v___y_2290_ = v___x_2342_;
goto v___jp_2289_;
}
else
{
v___y_2290_ = v___y_2344_;
goto v___jp_2289_;
}
}
v___jp_2345_:
{
if (lean_obj_tag(v_code_2287_) == 6)
{
v___y_2344_ = v_a_2346_;
goto v___jp_2343_;
}
else
{
if (v___x_2342_ == 0)
{
v___y_2290_ = v_a_2346_;
goto v___jp_2289_;
}
else
{
v___y_2344_ = v_a_2346_;
goto v___jp_2343_;
}
}
}
}
else
{
lean_object* v_code_2363_; lean_object* v___x_2364_; 
v_code_2363_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc_ref(v_code_2363_);
v___x_2364_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2363_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___x_2364_);
lean_inc_ref(v_a_2272_);
v___x_2366_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2272_, v_a_2365_);
v_a_2274_ = v___x_2366_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v_as_2260_);
lean_dec(v_i_2259_);
lean_dec(v_fvarId_2256_);
v_a_2367_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2364_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2364_);
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
v___jp_2273_:
{
size_t v___x_2275_; size_t v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = lean_ptr_addr(v_a_2272_);
v___x_2276_ = lean_ptr_addr(v_a_2274_);
v___x_2277_ = lean_usize_dec_eq(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_add(v_i_2259_, v___x_2278_);
v___x_2280_ = lean_array_fset(v_as_2260_, v_i_2259_, v_a_2274_);
lean_dec(v_i_2259_);
v_i_2259_ = v___x_2279_;
v_as_2260_ = v___x_2280_;
goto _start;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_a_2274_);
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_nat_add(v_i_2259_, v___x_2282_);
lean_dec(v_i_2259_);
v_i_2259_ = v___x_2283_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2421_; uint8_t v___y_2422_; lean_object* v_decl_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2472_; uint8_t v___y_2473_; lean_object* v_decl_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2493_; lean_object* v___y_2494_; uint8_t v___y_2495_; lean_object* v_fileName_2499_; lean_object* v_fileMap_2500_; lean_object* v_options_2501_; lean_object* v_currRecDepth_2502_; lean_object* v_maxRecDepth_2503_; lean_object* v_ref_2504_; lean_object* v_currNamespace_2505_; lean_object* v_openDecls_2506_; lean_object* v_initHeartbeats_2507_; lean_object* v_maxHeartbeats_2508_; lean_object* v_quotContext_2509_; lean_object* v_currMacroScope_2510_; uint8_t v_diag_2511_; lean_object* v_cancelTk_x3f_2512_; uint8_t v_suppressElabErrors_2513_; lean_object* v_inheritedTraceOptions_2514_; uint8_t v___x_2515_; 
v_fileName_2499_ = lean_ctor_get(v_a_2381_, 0);
v_fileMap_2500_ = lean_ctor_get(v_a_2381_, 1);
v_options_2501_ = lean_ctor_get(v_a_2381_, 2);
v_currRecDepth_2502_ = lean_ctor_get(v_a_2381_, 3);
v_maxRecDepth_2503_ = lean_ctor_get(v_a_2381_, 4);
v_ref_2504_ = lean_ctor_get(v_a_2381_, 5);
v_currNamespace_2505_ = lean_ctor_get(v_a_2381_, 6);
v_openDecls_2506_ = lean_ctor_get(v_a_2381_, 7);
v_initHeartbeats_2507_ = lean_ctor_get(v_a_2381_, 8);
v_maxHeartbeats_2508_ = lean_ctor_get(v_a_2381_, 9);
v_quotContext_2509_ = lean_ctor_get(v_a_2381_, 10);
v_currMacroScope_2510_ = lean_ctor_get(v_a_2381_, 11);
v_diag_2511_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*14);
v_cancelTk_x3f_2512_ = lean_ctor_get(v_a_2381_, 12);
v_suppressElabErrors_2513_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2514_ = lean_ctor_get(v_a_2381_, 13);
v___x_2515_ = lean_nat_dec_eq(v_currRecDepth_2502_, v_maxRecDepth_2503_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_3283_; 
lean_inc_ref(v_inheritedTraceOptions_2514_);
lean_inc(v_cancelTk_x3f_2512_);
lean_inc(v_currMacroScope_2510_);
lean_inc(v_quotContext_2509_);
lean_inc(v_maxHeartbeats_2508_);
lean_inc(v_initHeartbeats_2507_);
lean_inc(v_openDecls_2506_);
lean_inc(v_currNamespace_2505_);
lean_inc(v_ref_2504_);
lean_inc(v_maxRecDepth_2503_);
lean_inc(v_currRecDepth_2502_);
lean_inc_ref(v_options_2501_);
lean_inc_ref(v_fileMap_2500_);
lean_inc_ref(v_fileName_2499_);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_a_2381_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; lean_object* v_unused_3285_; lean_object* v_unused_3286_; lean_object* v_unused_3287_; lean_object* v_unused_3288_; lean_object* v_unused_3289_; lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; lean_object* v_unused_3295_; lean_object* v_unused_3296_; lean_object* v_unused_3297_; 
v_unused_3284_ = lean_ctor_get(v_a_2381_, 13);
lean_dec(v_unused_3284_);
v_unused_3285_ = lean_ctor_get(v_a_2381_, 12);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_a_2381_, 11);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_a_2381_, 10);
lean_dec(v_unused_3287_);
v_unused_3288_ = lean_ctor_get(v_a_2381_, 9);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_a_2381_, 8);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_a_2381_, 7);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_a_2381_, 6);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_a_2381_, 5);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_a_2381_, 4);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_a_2381_, 3);
lean_dec(v_unused_3294_);
v_unused_3295_ = lean_ctor_get(v_a_2381_, 2);
lean_dec(v_unused_3295_);
v_unused_3296_ = lean_ctor_get(v_a_2381_, 1);
lean_dec(v_unused_3296_);
v_unused_3297_ = lean_ctor_get(v_a_2381_, 0);
lean_dec(v_unused_3297_);
v___x_2517_ = v_a_2381_;
v_isShared_2518_ = v_isSharedCheck_3283_;
goto v_resetjp_2516_;
}
else
{
lean_dec(v_a_2381_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_3283_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2377_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_3273_; 
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; 
v_unused_3274_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_3274_);
v___x_2521_ = v___x_2519_;
v_isShared_2522_ = v_isSharedCheck_3273_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2519_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_3273_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_decl_2524_; lean_object* v_k_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_unsigned_to_nat(1u);
v___x_2598_ = lean_nat_add(v_currRecDepth_2502_, v___x_2597_);
lean_inc(v_maxRecDepth_2503_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 3, v___x_2598_);
v___x_2600_ = v___x_2517_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_fileName_2499_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_fileMap_2500_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_options_2501_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_maxRecDepth_2503_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_ref_2504_);
lean_ctor_set(v_reuseFailAlloc_3272_, 6, v_currNamespace_2505_);
lean_ctor_set(v_reuseFailAlloc_3272_, 7, v_openDecls_2506_);
lean_ctor_set(v_reuseFailAlloc_3272_, 8, v_initHeartbeats_2507_);
lean_ctor_set(v_reuseFailAlloc_3272_, 9, v_maxHeartbeats_2508_);
lean_ctor_set(v_reuseFailAlloc_3272_, 10, v_quotContext_2509_);
lean_ctor_set(v_reuseFailAlloc_3272_, 11, v_currMacroScope_2510_);
lean_ctor_set(v_reuseFailAlloc_3272_, 12, v_cancelTk_x3f_2512_);
lean_ctor_set(v_reuseFailAlloc_3272_, 13, v_inheritedTraceOptions_2514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3272_, sizeof(void*)*14, v_diag_2511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3272_, sizeof(void*)*14 + 1, v_suppressElabErrors_2513_);
v___x_2600_ = v_reuseFailAlloc_3272_;
goto v_reusejp_2599_;
}
v___jp_2523_:
{
lean_object* v_fvarId_2533_; lean_object* v_params_2534_; lean_object* v_type_2535_; lean_object* v___x_2536_; 
v_fvarId_2533_ = lean_ctor_get(v_decl_2524_, 0);
v_params_2534_ = lean_ctor_get(v_decl_2524_, 2);
v_type_2535_ = lean_ctor_get(v_decl_2524_, 3);
v___x_2536_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2533_, v___y_2527_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; uint8_t v___x_2538_; uint8_t v___x_2539_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = 0;
v___x_2539_ = lean_unbox(v_a_2537_);
if (v___x_2539_ == 0)
{
uint8_t v___x_2540_; 
v___x_2540_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2375_);
if (v___x_2540_ == 0)
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
v___y_2472_ = v_k_2525_;
v___y_2473_ = v___x_2541_;
v_decl_2474_ = v_decl_2524_;
v___y_2475_ = v___y_2526_;
v___y_2476_ = v___y_2527_;
v___y_2477_ = v___y_2528_;
v___y_2478_ = v___y_2529_;
v___y_2479_ = v___y_2530_;
v___y_2480_ = v___y_2531_;
v___y_2481_ = v___y_2532_;
goto v___jp_2471_;
}
else
{
uint8_t v___x_2542_; 
lean_inc_ref(v_type_2535_);
v___x_2542_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2535_, v_params_2534_);
if (v___x_2542_ == 0)
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
v___y_2472_ = v_k_2525_;
v___y_2473_ = v___x_2543_;
v_decl_2474_ = v_decl_2524_;
v___y_2475_ = v___y_2526_;
v___y_2476_ = v___y_2527_;
v___y_2477_ = v___y_2528_;
v___y_2478_ = v___y_2529_;
v___y_2479_ = v___y_2530_;
v___y_2480_ = v___y_2531_;
v___y_2481_ = v___y_2532_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2544_; lean_object* v_subst_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_st_ref_get(v___y_2527_);
v_subst_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_subst_2545_);
lean_dec(v___x_2544_);
v___x_2546_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2538_, v___x_2515_, v_decl_2524_, v_subst_2545_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v_subst_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
v___x_2548_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2547_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2527_);
if (lean_obj_tag(v___x_2550_) == 0)
{
uint8_t v___x_2551_; 
lean_dec_ref(v___x_2550_);
v___x_2551_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
v___y_2472_ = v_k_2525_;
v___y_2473_ = v___x_2551_;
v_decl_2474_ = v_a_2549_;
v___y_2475_ = v___y_2526_;
v___y_2476_ = v___y_2527_;
v___y_2477_ = v___y_2528_;
v___y_2478_ = v___y_2529_;
v___y_2479_ = v___y_2530_;
v___y_2480_ = v___y_2531_;
v___y_2481_ = v___y_2532_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_a_2549_);
lean_dec(v_a_2537_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_k_2525_);
lean_dec_ref(v_code_2375_);
v_a_2552_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2550_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2550_);
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
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2537_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_k_2525_);
lean_dec_ref(v_code_2375_);
v_a_2560_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2548_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2548_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_a_2537_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_k_2525_);
lean_dec_ref(v_code_2375_);
v_a_2568_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2546_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2546_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
else
{
lean_object* v___x_2576_; lean_object* v_subst_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_st_ref_get(v___y_2527_);
v_subst_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc_ref(v_subst_2577_);
lean_dec(v___x_2576_);
v___x_2578_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2538_, v___x_2515_, v_decl_2524_, v_subst_2577_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v_subst_2577_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; uint8_t v___x_2580_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref(v___x_2578_);
v___x_2580_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
v___y_2421_ = v_k_2525_;
v___y_2422_ = v___x_2580_;
v_decl_2423_ = v_a_2579_;
v___y_2424_ = v___y_2526_;
v___y_2425_ = v___y_2527_;
v___y_2426_ = v___y_2528_;
v___y_2427_ = v___y_2529_;
v___y_2428_ = v___y_2530_;
v___y_2429_ = v___y_2531_;
v___y_2430_ = v___y_2532_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2537_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_k_2525_);
lean_dec_ref(v_code_2375_);
v_a_2581_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2578_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2578_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_k_2525_);
lean_dec_ref(v_decl_2524_);
lean_dec_ref(v_code_2375_);
v_a_2589_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2536_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2536_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
v_reusejp_2599_:
{
switch(lean_obj_tag(v_code_2375_))
{
case 0:
{
lean_object* v_decl_2601_; lean_object* v_k_2602_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2612_; uint8_t v___x_2826_; lean_object* v_decl_2828_; lean_object* v_type_2829_; lean_object* v_value_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___x_2841_; 
lean_del_object(v___x_2521_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
v_decl_2601_ = lean_ctor_get(v_code_2375_, 0);
v_k_2602_ = lean_ctor_get(v_code_2375_, 1);
v___x_2826_ = 0;
lean_inc_ref(v_decl_2601_);
v___x_2841_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_2826_, v___x_2515_, v_decl_2601_, v_a_2377_, v_a_2380_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; uint8_t v___x_2895_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2895_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_2826_, v_decl_2601_, v_a_2842_);
if (v___x_2895_ == 0)
{
goto v___jp_2885_;
}
else
{
if (v___x_2515_ == 0)
{
v___y_2844_ = v_a_2376_;
v___y_2845_ = v_a_2377_;
v___y_2846_ = v_a_2378_;
v___y_2847_ = v_a_2379_;
v___y_2848_ = v_a_2380_;
v___y_2849_ = v___x_2600_;
v___y_2850_ = v_a_2382_;
goto v___jp_2843_;
}
else
{
goto v___jp_2885_;
}
}
v___jp_2843_:
{
lean_object* v_type_2851_; lean_object* v_value_2852_; lean_object* v___x_2853_; 
v_type_2851_ = lean_ctor_get(v_a_2842_, 2);
v_value_2852_ = lean_ctor_get(v_a_2842_, 3);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc_ref(v___y_2846_);
lean_inc(v_value_2852_);
v___x_2853_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2852_, v___y_2844_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref(v___x_2853_);
if (lean_obj_tag(v_a_2854_) == 1)
{
lean_object* v_val_2855_; lean_object* v___x_2856_; 
v_val_2855_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref(v_a_2854_);
v___x_2856_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2845_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref(v___x_2856_);
v___x_2857_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2826_, v_a_2842_, v_val_2855_, v___y_2848_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_type_2859_; lean_object* v_value_2860_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
v_type_2859_ = lean_ctor_get(v_a_2858_, 2);
lean_inc_ref(v_type_2859_);
v_value_2860_ = lean_ctor_get(v_a_2858_, 3);
lean_inc(v_value_2860_);
v_decl_2828_ = v_a_2858_;
v_type_2829_ = v_type_2859_;
v_value_2830_ = v_value_2860_;
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2845_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
v___y_2836_ = v___y_2849_;
v___y_2837_ = v___y_2850_;
goto v___jp_2827_;
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v_code_2375_);
v_a_2861_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2857_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2857_);
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
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_val_2855_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_code_2375_);
v_a_2869_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2856_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2856_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_inc(v_value_2852_);
lean_inc_ref(v_type_2851_);
lean_dec(v_a_2854_);
v_decl_2828_ = v_a_2842_;
v_type_2829_ = v_type_2851_;
v_value_2830_ = v_value_2852_;
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2845_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
v___y_2836_ = v___y_2849_;
v___y_2837_ = v___y_2850_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_code_2375_);
v_a_2877_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2853_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2853_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
v___jp_2885_:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2377_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_dec_ref(v___x_2886_);
v___y_2844_ = v_a_2376_;
v___y_2845_ = v_a_2377_;
v___y_2846_ = v_a_2378_;
v___y_2847_ = v_a_2379_;
v___y_2848_ = v_a_2380_;
v___y_2849_ = v___x_2600_;
v___y_2850_ = v_a_2382_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2886_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_2896_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2841_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2841_);
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
v___jp_2603_:
{
if (v___y_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2605_);
v___x_2613_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2605_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
if (lean_obj_tag(v_a_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v___x_2616_; 
lean_inc_ref(v_k_2602_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_code_2375_);
v_val_2615_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref(v_a_2614_);
v___x_2616_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2609_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v___x_2616_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2607_);
v___x_2617_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2602_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2615_, v_a_2618_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2607_);
lean_dec(v_val_2615_);
return v___x_2619_;
}
else
{
lean_dec(v_val_2615_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
return v___x_2617_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_val_2615_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
v_a_2620_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2616_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2616_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v___x_2628_; 
lean_dec(v_a_2614_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2605_);
v___x_2628_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2605_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
if (lean_obj_tag(v_a_2629_) == 1)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2638_; 
lean_inc_ref(v_k_2602_);
lean_dec_ref(v___y_2605_);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; lean_object* v_unused_2640_; 
v_unused_2639_ = lean_ctor_get(v_code_2375_, 1);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_2640_);
v___x_2631_ = v_code_2375_;
v_isShared_2632_ = v_isSharedCheck_2638_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_code_2375_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2638_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_val_2633_; lean_object* v___x_2635_; 
v_val_2633_ = lean_ctor_get(v_a_2629_, 0);
lean_inc(v_val_2633_);
lean_dec_ref(v_a_2629_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 1);
lean_ctor_set(v___x_2631_, 0, v_val_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_val_2633_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2602_);
v___x_2635_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
v_code_2375_ = v___x_2635_;
v_a_2376_ = v___y_2607_;
v_a_2377_ = v___y_2609_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2604_;
v_a_2380_ = v___y_2608_;
v_a_2381_ = v___y_2610_;
v_a_2382_ = v___y_2611_;
goto _start;
}
}
}
else
{
lean_object* v_fvarId_2641_; lean_object* v_value_2642_; lean_object* v___x_2643_; 
lean_dec(v_a_2629_);
v_fvarId_2641_ = lean_ctor_get(v___y_2605_, 0);
v_value_2642_ = lean_ctor_get(v___y_2605_, 3);
v___x_2643_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
if (lean_obj_tag(v_a_2644_) == 1)
{
lean_object* v_val_2645_; lean_object* v___x_2646_; 
lean_inc_ref(v_k_2602_);
lean_dec_ref(v_code_2375_);
v_val_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc(v_val_2645_);
lean_dec_ref(v_a_2644_);
lean_inc(v_fvarId_2641_);
v___x_2646_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2641_, v_val_2645_, v___y_2609_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2647_; 
lean_dec_ref(v___x_2646_);
v___x_2647_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2605_, v___y_2609_, v___y_2608_);
lean_dec_ref(v___y_2605_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_dec_ref(v___x_2647_);
v_code_2375_ = v_k_2602_;
v_a_2376_ = v___y_2607_;
v_a_2377_ = v___y_2609_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2604_;
v_a_2380_ = v___y_2608_;
v_a_2381_ = v___y_2610_;
v_a_2382_ = v___y_2611_;
goto _start;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
v_a_2649_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2647_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2647_);
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
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
v_a_2657_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2646_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2646_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v___x_2665_; 
lean_dec(v_a_2644_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2607_);
lean_inc_ref(v_k_2602_);
lean_inc_ref(v___y_2605_);
v___x_2665_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2605_, v_k_2602_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2665_);
if (lean_obj_tag(v_a_2666_) == 1)
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_val_2667_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v_a_2666_);
v___x_2668_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2605_, v___y_2609_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2605_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2668_, 0);
lean_dec(v_unused_2676_);
v___x_2670_ = v___x_2668_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v___x_2668_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_val_2667_);
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_val_2667_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_val_2667_);
v_a_2677_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2668_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2668_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v___x_2685_; 
lean_dec(v_a_2666_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2607_);
lean_inc(v_value_2642_);
v___x_2685_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2642_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v___x_2685_);
if (lean_obj_tag(v_a_2686_) == 1)
{
lean_object* v_val_2687_; lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2690_; 
lean_inc_ref(v_k_2602_);
lean_dec_ref(v_code_2375_);
v_val_2687_ = lean_ctor_get(v_a_2686_, 0);
lean_inc(v_val_2687_);
lean_dec_ref(v_a_2686_);
v_fst_2688_ = lean_ctor_get(v_val_2687_, 0);
lean_inc(v_fst_2688_);
v_snd_2689_ = lean_ctor_get(v_val_2687_, 1);
lean_inc(v_snd_2689_);
lean_dec(v_val_2687_);
lean_inc(v_fvarId_2641_);
v___x_2690_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2641_, v_snd_2689_, v___y_2609_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2691_; 
lean_dec_ref(v___x_2690_);
v___x_2691_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2605_, v___y_2609_, v___y_2608_);
lean_dec_ref(v___y_2605_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v___x_2691_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2607_);
v___x_2692_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2602_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2688_, v_a_2693_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2607_);
lean_dec(v_fst_2688_);
return v___x_2694_;
}
else
{
lean_dec(v_fst_2688_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
return v___x_2692_;
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_fst_2688_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
v_a_2695_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2691_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2691_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_fst_2688_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
v_a_2703_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2690_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2690_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v___x_2711_; 
lean_dec(v_a_2686_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2604_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2607_);
lean_inc_ref(v_k_2602_);
v___x_2711_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2602_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2641_, v___y_2609_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; uint8_t v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = lean_unbox(v_a_2714_);
lean_dec(v_a_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v___x_2716_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2605_, v___y_2609_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2605_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v___x_2716_, 0);
lean_dec(v_unused_2724_);
v___x_2718_ = v___x_2716_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_dec(v___x_2716_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_a_2712_);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2712_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2712_);
v_a_2725_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2716_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2716_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2733_; 
lean_inc_ref(v___y_2605_);
v___x_2733_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2605_, v___y_2607_, v___y_2609_, v___y_2606_, v___y_2604_, v___y_2608_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2733_) == 0)
{
size_t v___x_2734_; size_t v___x_2735_; uint8_t v___x_2736_; 
lean_dec_ref(v___x_2733_);
v___x_2734_ = lean_ptr_addr(v_k_2602_);
v___x_2735_ = lean_ptr_addr(v_a_2712_);
v___x_2736_ = lean_usize_dec_eq(v___x_2734_, v___x_2735_);
if (v___x_2736_ == 0)
{
v___y_2493_ = v___y_2605_;
v___y_2494_ = v_a_2712_;
v___y_2495_ = v___x_2736_;
goto v___jp_2492_;
}
else
{
size_t v___x_2737_; size_t v___x_2738_; uint8_t v___x_2739_; 
v___x_2737_ = lean_ptr_addr(v_decl_2601_);
v___x_2738_ = lean_ptr_addr(v___y_2605_);
v___x_2739_ = lean_usize_dec_eq(v___x_2737_, v___x_2738_);
v___y_2493_ = v___y_2605_;
v___y_2494_ = v_a_2712_;
v___y_2495_ = v___x_2739_;
goto v___jp_2492_;
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_a_2712_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_code_2375_);
v_a_2740_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2733_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2733_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2712_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2748_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2713_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2713_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
return v___x_2711_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2756_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2685_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2685_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2764_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2665_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2665_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2772_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2643_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2643_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2780_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2628_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2628_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_code_2375_);
v_a_2788_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2613_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2613_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v___x_2796_; lean_object* v_fvarId_2797_; lean_object* v_subst_2798_; lean_object* v_used_2799_; lean_object* v_binderRenaming_2800_; lean_object* v_funDeclInfoMap_2801_; uint8_t v_simplified_2802_; lean_object* v_visited_2803_; lean_object* v_inline_2804_; lean_object* v_inlineLocal_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2825_; 
lean_inc_ref(v_k_2602_);
lean_dec_ref(v_code_2375_);
v___x_2796_ = lean_st_ref_take(v___y_2609_);
v_fvarId_2797_ = lean_ctor_get(v___y_2605_, 0);
v_subst_2798_ = lean_ctor_get(v___x_2796_, 0);
v_used_2799_ = lean_ctor_get(v___x_2796_, 1);
v_binderRenaming_2800_ = lean_ctor_get(v___x_2796_, 2);
v_funDeclInfoMap_2801_ = lean_ctor_get(v___x_2796_, 3);
v_simplified_2802_ = lean_ctor_get_uint8(v___x_2796_, sizeof(void*)*7);
v_visited_2803_ = lean_ctor_get(v___x_2796_, 4);
v_inline_2804_ = lean_ctor_get(v___x_2796_, 5);
v_inlineLocal_2805_ = lean_ctor_get(v___x_2796_, 6);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2807_ = v___x_2796_;
v_isShared_2808_ = v_isSharedCheck_2825_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_inlineLocal_2805_);
lean_inc(v_inline_2804_);
lean_inc(v_visited_2803_);
lean_inc(v_funDeclInfoMap_2801_);
lean_inc(v_binderRenaming_2800_);
lean_inc(v_used_2799_);
lean_inc(v_subst_2798_);
lean_dec(v___x_2796_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2825_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_box(0);
lean_inc(v_fvarId_2797_);
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2798_, v_fvarId_2797_, v___x_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_used_2799_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_binderRenaming_2800_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_funDeclInfoMap_2801_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_visited_2803_);
lean_ctor_set(v_reuseFailAlloc_2824_, 5, v_inline_2804_);
lean_ctor_set(v_reuseFailAlloc_2824_, 6, v_inlineLocal_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2824_, sizeof(void*)*7, v_simplified_2802_);
v___x_2812_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_st_ref_set(v___y_2609_, v___x_2812_);
v___x_2814_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2605_, v___y_2609_, v___y_2608_);
lean_dec_ref(v___y_2605_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref(v___x_2814_);
v_code_2375_ = v_k_2602_;
v_a_2376_ = v___y_2607_;
v_a_2377_ = v___y_2609_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2604_;
v_a_2380_ = v___y_2608_;
v_a_2381_ = v___y_2610_;
v_a_2382_ = v___y_2611_;
goto _start;
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_k_2602_);
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
v___jp_2827_:
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Expr_isErased(v_type_2829_);
lean_dec_ref(v_type_2829_);
if (v___x_2838_ == 0)
{
lean_dec(v_value_2830_);
v___y_2604_ = v___y_2834_;
v___y_2605_ = v_decl_2828_;
v___y_2606_ = v___y_2833_;
v___y_2607_ = v___y_2831_;
v___y_2608_ = v___y_2835_;
v___y_2609_ = v___y_2832_;
v___y_2610_ = v___y_2836_;
v___y_2611_ = v___y_2837_;
v___y_2612_ = v___x_2515_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = lean_box(1);
v___x_2840_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___x_2826_, v_value_2830_, v___x_2839_);
lean_dec(v_value_2830_);
if (v___x_2840_ == 0)
{
v___y_2604_ = v___y_2834_;
v___y_2605_ = v_decl_2828_;
v___y_2606_ = v___y_2833_;
v___y_2607_ = v___y_2831_;
v___y_2608_ = v___y_2835_;
v___y_2609_ = v___y_2832_;
v___y_2610_ = v___y_2836_;
v___y_2611_ = v___y_2837_;
v___y_2612_ = v___x_2838_;
goto v___jp_2603_;
}
else
{
v___y_2604_ = v___y_2834_;
v___y_2605_ = v_decl_2828_;
v___y_2606_ = v___y_2833_;
v___y_2607_ = v___y_2831_;
v___y_2608_ = v___y_2835_;
v___y_2609_ = v___y_2832_;
v___y_2610_ = v___y_2836_;
v___y_2611_ = v___y_2837_;
v___y_2612_ = v___x_2515_;
goto v___jp_2603_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_2904_; lean_object* v_args_2905_; lean_object* v___x_2906_; lean_object* v_subst_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; 
lean_del_object(v___x_2521_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
v_fvarId_2904_ = lean_ctor_get(v_code_2375_, 0);
v_args_2905_ = lean_ctor_get(v_code_2375_, 1);
v___x_2906_ = lean_st_ref_get(v_a_2377_);
v_subst_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_ref(v_subst_2907_);
lean_dec(v___x_2906_);
v___x_2908_ = 0;
lean_inc(v_fvarId_2904_);
v___x_2909_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2907_, v_fvarId_2904_, v___x_2515_);
lean_dec_ref(v_subst_2907_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_fvarId_2910_; lean_object* v___x_2911_; 
v_fvarId_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_fvarId_2910_);
lean_dec_ref(v___x_2909_);
lean_inc_ref(v_args_2905_);
v___x_2911_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_2908_, v___x_2515_, v_args_2905_, v_a_2377_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2980_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2980_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2980_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
uint8_t v___y_2917_; lean_object* v___y_2939_; lean_object* v___x_2948_; 
lean_inc(v_a_2382_);
lean_inc_ref(v___x_2600_);
lean_inc(v_a_2380_);
lean_inc_ref(v_a_2379_);
lean_inc(v_a_2912_);
v___x_2948_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_2910_, v_a_2912_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
if (lean_obj_tag(v_a_2949_) == 1)
{
lean_object* v_val_2950_; 
lean_del_object(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v_fvarId_2910_);
lean_dec_ref(v_code_2375_);
v_val_2950_ = lean_ctor_get(v_a_2949_, 0);
lean_inc(v_val_2950_);
lean_dec_ref(v_a_2949_);
v_code_2375_ = v_val_2950_;
v_a_2381_ = v___x_2600_;
goto _start;
}
else
{
lean_object* v___x_2952_; 
lean_dec(v_a_2949_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_a_2376_);
lean_inc(v_fvarId_2910_);
v___x_2952_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_2910_, v_a_2377_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
lean_dec_ref(v___x_2952_);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = lean_array_get_size(v_a_2912_);
v___x_2955_ = lean_nat_dec_lt(v___x_2953_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_dec(v_a_2377_);
goto v___jp_2933_;
}
else
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_nat_dec_le(v___x_2954_, v___x_2954_);
if (v___x_2957_ == 0)
{
if (v___x_2955_ == 0)
{
lean_dec(v_a_2377_);
goto v___jp_2933_;
}
else
{
size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = lean_usize_of_nat(v___x_2954_);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_2912_, v___x_2958_, v___x_2959_, v___x_2956_, v_a_2377_);
lean_dec(v_a_2377_);
v___y_2939_ = v___x_2960_;
goto v___jp_2938_;
}
}
else
{
size_t v___x_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = lean_usize_of_nat(v___x_2954_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_2912_, v___x_2961_, v___x_2962_, v___x_2956_, v_a_2377_);
lean_dec(v_a_2377_);
v___y_2939_ = v___x_2963_;
goto v___jp_2938_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v_fvarId_2910_);
lean_dec_ref(v_code_2375_);
lean_dec(v_a_2377_);
v_a_2964_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2952_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2952_);
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
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_del_object(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v_fvarId_2910_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_2972_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2948_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2948_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
v___jp_2916_:
{
if (v___y_2917_ == 0)
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2927_; 
v_isSharedCheck_2927_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; lean_object* v_unused_2929_; 
v_unused_2928_ = lean_ctor_get(v_code_2375_, 1);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_2929_);
v___x_2919_ = v_code_2375_;
v_isShared_2920_ = v_isSharedCheck_2927_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_code_2375_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2927_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v_a_2912_);
lean_ctor_set(v___x_2919_, 0, v_fvarId_2910_);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_fvarId_2910_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_a_2912_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2922_);
v___x_2924_ = v___x_2914_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
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
else
{
lean_object* v___x_2931_; 
lean_dec(v_a_2912_);
lean_dec(v_fvarId_2910_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v_code_2375_);
v___x_2931_ = v___x_2914_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_code_2375_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
v___jp_2933_:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_instBEqFVarId_beq(v_fvarId_2904_, v_fvarId_2910_);
if (v___x_2934_ == 0)
{
v___y_2917_ = v___x_2934_;
goto v___jp_2916_;
}
else
{
size_t v___x_2935_; size_t v___x_2936_; uint8_t v___x_2937_; 
v___x_2935_ = lean_ptr_addr(v_args_2905_);
v___x_2936_ = lean_ptr_addr(v_a_2912_);
v___x_2937_ = lean_usize_dec_eq(v___x_2935_, v___x_2936_);
v___y_2917_ = v___x_2937_;
goto v___jp_2916_;
}
}
v___jp_2938_:
{
if (lean_obj_tag(v___y_2939_) == 0)
{
lean_dec_ref(v___y_2939_);
goto v___jp_2933_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_del_object(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v_fvarId_2910_);
lean_dec_ref(v_code_2375_);
v_a_2940_ = lean_ctor_get(v___y_2939_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___y_2939_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___y_2939_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___y_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_fvarId_2910_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_2981_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2911_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2911_);
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
else
{
lean_object* v___x_2989_; 
lean_dec_ref(v_code_2375_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v___x_2989_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2908_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v___x_2989_;
}
}
case 4:
{
lean_object* v_cases_2990_; lean_object* v___x_2991_; 
lean_del_object(v___x_2521_);
v_cases_2990_ = lean_ctor_get(v_code_2375_, 0);
lean_inc_ref(v_cases_2990_);
lean_inc(v_a_2382_);
lean_inc_ref(v___x_2600_);
lean_inc(v_a_2380_);
lean_inc_ref(v_a_2379_);
lean_inc_ref(v_a_2378_);
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc_ref(v_cases_2990_);
v___x_2991_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_2990_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3203_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_3203_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3203_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
if (lean_obj_tag(v_a_2992_) == 1)
{
lean_object* v_val_2996_; lean_object* v___x_2998_; 
lean_dec_ref(v_code_2375_);
lean_dec_ref(v_cases_2990_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_val_2996_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_val_2996_);
lean_dec_ref(v_a_2992_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v_val_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_val_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v_typeName_3000_; lean_object* v_resultType_3001_; lean_object* v_discr_3002_; lean_object* v_alts_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_2992_);
v_typeName_3000_ = lean_ctor_get(v_cases_2990_, 0);
v_resultType_3001_ = lean_ctor_get(v_cases_2990_, 1);
v_discr_3002_ = lean_ctor_get(v_cases_2990_, 2);
v_alts_3003_ = lean_ctor_get(v_cases_2990_, 3);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_cases_2990_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3005_ = v_cases_2990_;
v_isShared_3006_ = v_isSharedCheck_3202_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_alts_3003_);
lean_inc(v_discr_3002_);
lean_inc(v_resultType_3001_);
lean_inc(v_typeName_3000_);
lean_dec(v_cases_2990_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3202_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v_subst_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3007_ = lean_st_ref_get(v_a_2377_);
v_subst_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_ref(v_subst_3008_);
lean_dec(v___x_3007_);
v___x_3009_ = 0;
lean_inc(v_discr_3002_);
v___x_3010_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3008_, v_discr_3002_, v___x_2515_);
lean_dec_ref(v_subst_3008_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_fvarId_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3200_; 
v_fvarId_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3200_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_fvarId_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3200_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_st_ref_get(v_a_2377_);
v___x_3016_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2382_);
lean_inc_ref(v___x_2600_);
lean_inc(v_a_2380_);
lean_inc_ref(v_a_2379_);
lean_inc_ref(v_a_2378_);
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc_ref(v_alts_3003_);
lean_inc(v_fvarId_3011_);
v___x_3017_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3011_, v_currRecDepth_2502_, v_maxRecDepth_2503_, v___x_3016_, v_alts_3003_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3191_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3191_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3191_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; 
lean_inc(v_a_2382_);
lean_inc_ref(v___x_2600_);
lean_inc(v_a_2380_);
lean_inc_ref(v_a_2379_);
lean_inc(v_a_2377_);
v___x_3022_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3018_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3182_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3182_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3182_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_subst_3027_; lean_object* v___x_3028_; lean_object* v___y_3030_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3087_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v_subst_3027_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_ref(v_subst_3027_);
lean_dec(v___x_3015_);
lean_inc_ref(v_resultType_3001_);
v___x_3028_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3009_, v_subst_3027_, v___x_2515_, v_resultType_3001_);
lean_dec_ref(v_subst_3027_);
v___x_3118_ = lean_array_get_size(v_a_3023_);
v___x_3119_ = lean_nat_dec_eq(v___x_3118_, v___x_2597_);
if (v___x_3119_ == 0)
{
lean_del_object(v___x_2994_);
v___y_3093_ = v_a_2377_;
v___y_3094_ = v_a_2379_;
v___y_3095_ = v_a_2380_;
v___y_3096_ = v___x_2600_;
v___y_3097_ = v_a_2382_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_array_fget_borrowed(v_a_3023_, v___x_3016_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_params_3121_; lean_object* v_code_3122_; lean_object* v___y_3142_; lean_object* v___x_3151_; uint8_t v_a_3163_; uint8_t v___x_3164_; 
lean_del_object(v___x_2994_);
v_params_3121_ = lean_ctor_get(v___x_3120_, 1);
v_code_3122_ = lean_ctor_get(v___x_3120_, 2);
v___x_3151_ = lean_array_get_size(v_params_3121_);
v___x_3164_ = lean_nat_dec_lt(v___x_3016_, v___x_3151_);
if (v___x_3164_ == 0)
{
v_a_3163_ = v___x_2515_;
goto v___jp_3162_;
}
else
{
if (v___x_3164_ == 0)
{
v_a_3163_ = v___x_2515_;
goto v___jp_3162_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3151_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3121_, v___x_3165_, v___x_3166_, v_a_2377_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; uint8_t v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = lean_unbox(v_a_3168_);
lean_dec(v_a_3168_);
v_a_3163_ = v___x_3169_;
goto v___jp_3162_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_del_object(v___x_3020_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2377_);
v_a_3170_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3167_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3167_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
v___jp_3123_:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2377_);
lean_dec(v_a_2377_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_3124_, 0);
lean_dec(v_unused_3132_);
v___x_3126_ = v___x_3124_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v___x_3124_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v_code_3122_);
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_code_3122_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v_code_3122_);
v_a_3133_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3124_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3124_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
v___jp_3141_:
{
if (lean_obj_tag(v___y_3142_) == 0)
{
lean_dec_ref(v___y_3142_);
goto v___jp_3123_;
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v_code_3122_);
lean_dec(v_a_2377_);
v_a_3143_ = lean_ctor_get(v___y_3142_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___y_3142_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___y_3142_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___y_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
v___jp_3152_:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_lt(v___x_3016_, v___x_3151_);
if (v___x_3153_ == 0)
{
lean_dec_ref(v_params_3121_);
lean_dec(v_a_2380_);
goto v___jp_3123_;
}
else
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_nat_dec_le(v___x_3151_, v___x_3151_);
if (v___x_3155_ == 0)
{
if (v___x_3153_ == 0)
{
lean_dec_ref(v_params_3121_);
lean_dec(v_a_2380_);
goto v___jp_3123_;
}
else
{
size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = lean_usize_of_nat(v___x_3151_);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_params_3121_, v___x_3156_, v___x_3157_, v___x_3154_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_params_3121_);
v___y_3142_ = v___x_3158_;
goto v___jp_3141_;
}
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3151_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_params_3121_, v___x_3159_, v___x_3160_, v___x_3154_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_params_3121_);
v___y_3142_ = v___x_3161_;
goto v___jp_3141_;
}
}
}
v___jp_3162_:
{
if (v_a_3163_ == 0)
{
lean_inc_ref(v_code_3122_);
lean_inc_ref(v_params_3121_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_del_object(v___x_3020_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2379_);
goto v___jp_3152_;
}
else
{
if (v___x_2515_ == 0)
{
v___y_3093_ = v_a_2377_;
v___y_3094_ = v_a_2379_;
v___y_3095_ = v_a_2380_;
v___y_3096_ = v___x_2600_;
v___y_3097_ = v_a_2382_;
goto v___jp_3092_;
}
else
{
lean_inc_ref(v_code_3122_);
lean_inc_ref(v_params_3121_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_del_object(v___x_3020_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2379_);
goto v___jp_3152_;
}
}
}
}
else
{
lean_object* v_code_3178_; lean_object* v___x_3180_; 
lean_inc_ref(v___x_3120_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_del_object(v___x_3020_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2377_);
v_code_3178_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_code_3178_);
lean_dec_ref(v___x_3120_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v_code_3178_);
v___x_3180_ = v___x_2994_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_code_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
v___jp_3029_:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3030_);
lean_dec(v___y_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3042_);
v___x_3033_ = v___x_3031_;
v_isShared_3034_ = v_isSharedCheck_3041_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v___x_3031_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3041_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 6);
lean_ctor_set(v___x_3013_, 0, v___x_3028_);
v___x_3036_ = v___x_3013_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3028_);
v___x_3036_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3036_);
v___x_3038_ = v___x_3033_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3013_);
v_a_3043_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3031_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3031_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
v___jp_3051_:
{
if (lean_obj_tag(v___y_3053_) == 0)
{
lean_dec_ref(v___y_3053_);
v___y_3030_ = v___y_3052_;
goto v___jp_3029_;
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v___y_3052_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3013_);
v_a_3054_ = lean_ctor_get(v___y_3053_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___y_3053_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___y_3053_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___y_3053_);
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
uint8_t v___x_3069_; 
v___x_3069_ = lean_nat_dec_lt(v___x_3016_, v___y_3066_);
if (v___x_3069_ == 0)
{
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v_a_3023_);
v___y_3030_ = v___y_3068_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_nat_dec_le(v___y_3066_, v___y_3066_);
if (v___x_3071_ == 0)
{
if (v___x_3069_ == 0)
{
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v_a_3023_);
v___y_3030_ = v___y_3068_;
goto v___jp_3029_;
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = lean_usize_of_nat(v___y_3066_);
lean_dec(v___y_3066_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_a_3023_, v___x_3072_, v___x_3073_, v___x_3070_, v___y_3065_, v___y_3063_, v___y_3067_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3065_);
lean_dec(v_a_3023_);
v___y_3052_ = v___y_3068_;
v___y_3053_ = v___x_3074_;
goto v___jp_3051_;
}
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = lean_usize_of_nat(v___y_3066_);
lean_dec(v___y_3066_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_a_3023_, v___x_3075_, v___x_3076_, v___x_3070_, v___y_3065_, v___y_3063_, v___y_3067_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3065_);
lean_dec(v_a_3023_);
v___y_3052_ = v___y_3068_;
v___y_3053_ = v___x_3077_;
goto v___jp_3051_;
}
}
}
v___jp_3078_:
{
lean_object* v___x_3080_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 3, v_a_3023_);
lean_ctor_set(v___x_3005_, 2, v_fvarId_3011_);
lean_ctor_set(v___x_3005_, 1, v___x_3028_);
v___x_3080_ = v___x_3005_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_typeName_3000_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_fvarId_3011_);
lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_a_3023_);
v___x_3080_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3081_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3081_);
v___x_3083_ = v___x_3025_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
v___jp_3086_:
{
if (v___y_3087_ == 0)
{
lean_del_object(v___x_3020_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_code_2375_);
goto v___jp_3078_;
}
else
{
uint8_t v___x_3088_; 
v___x_3088_ = l_Lean_instBEqFVarId_beq(v_discr_3002_, v_fvarId_3011_);
lean_dec(v_discr_3002_);
if (v___x_3088_ == 0)
{
lean_del_object(v___x_3020_);
lean_dec_ref(v_code_2375_);
goto v___jp_3078_;
}
else
{
lean_object* v___x_3090_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec(v_typeName_3000_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_code_2375_);
v___x_3090_ = v___x_3020_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_code_2375_);
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
v___jp_3092_:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = lean_array_get_size(v_a_3023_);
v___x_3099_ = lean_nat_dec_lt(v___x_3016_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_del_object(v___x_3025_);
lean_del_object(v___x_3020_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___x_3098_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3093_;
goto v___jp_3062_;
}
else
{
if (v___x_3099_ == 0)
{
lean_del_object(v___x_3025_);
lean_del_object(v___x_3020_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___x_3098_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3093_;
goto v___jp_3062_;
}
else
{
size_t v___x_3100_; size_t v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = lean_usize_of_nat(v___x_3098_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_currRecDepth_2502_, v_maxRecDepth_2503_, v_a_3023_, v___x_3100_, v___x_3101_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
if (v___x_3102_ == 0)
{
lean_del_object(v___x_3025_);
lean_del_object(v___x_3020_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___x_3098_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3093_;
goto v___jp_3062_;
}
else
{
if (v___x_2515_ == 0)
{
lean_object* v___x_3103_; 
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_del_object(v___x_3013_);
lean_inc(v_fvarId_3011_);
v___x_3103_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3011_, v___y_3093_);
lean_dec(v___y_3093_);
if (lean_obj_tag(v___x_3103_) == 0)
{
size_t v___x_3104_; size_t v___x_3105_; uint8_t v___x_3106_; 
lean_dec_ref(v___x_3103_);
v___x_3104_ = lean_ptr_addr(v_alts_3003_);
lean_dec_ref(v_alts_3003_);
v___x_3105_ = lean_ptr_addr(v_a_3023_);
v___x_3106_ = lean_usize_dec_eq(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_dec_ref(v_resultType_3001_);
v___y_3087_ = v___x_3106_;
goto v___jp_3086_;
}
else
{
size_t v___x_3107_; size_t v___x_3108_; uint8_t v___x_3109_; 
v___x_3107_ = lean_ptr_addr(v_resultType_3001_);
lean_dec_ref(v_resultType_3001_);
v___x_3108_ = lean_ptr_addr(v___x_3028_);
v___x_3109_ = lean_usize_dec_eq(v___x_3107_, v___x_3108_);
v___y_3087_ = v___x_3109_;
goto v___jp_3086_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
lean_del_object(v___x_3020_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
v_a_3110_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3103_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3103_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_del_object(v___x_3025_);
lean_del_object(v___x_3020_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_dec_ref(v_code_2375_);
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3097_;
v___y_3065_ = v___y_3094_;
v___y_3066_ = v___x_3098_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3093_;
goto v___jp_3062_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_del_object(v___x_3020_);
lean_dec(v___x_3015_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_del_object(v___x_2994_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2377_);
v_a_3183_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3022_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3022_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v___x_3015_);
lean_del_object(v___x_3013_);
lean_dec(v_fvarId_3011_);
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_del_object(v___x_2994_);
lean_dec_ref(v_code_2375_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_3192_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3017_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3017_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
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
lean_object* v___x_3201_; 
lean_del_object(v___x_3005_);
lean_dec_ref(v_alts_3003_);
lean_dec(v_discr_3002_);
lean_dec_ref(v_resultType_3001_);
lean_dec(v_typeName_3000_);
lean_del_object(v___x_2994_);
lean_dec_ref(v_code_2375_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v___x_3201_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3009_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v___x_3201_;
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v_code_2375_);
lean_dec_ref(v_cases_2990_);
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
v_a_3204_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_2991_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_2991_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
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
case 5:
{
lean_object* v_fvarId_3212_; lean_object* v___x_3213_; lean_object* v_subst_3214_; lean_object* v___x_3215_; 
lean_del_object(v___x_2521_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_a_2376_);
v_fvarId_3212_ = lean_ctor_get(v_code_2375_, 0);
v___x_3213_ = lean_st_ref_get(v_a_2377_);
v_subst_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_ref(v_subst_3214_);
lean_dec(v___x_3213_);
lean_inc(v_fvarId_3212_);
v___x_3215_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3214_, v_fvarId_3212_, v___x_2515_);
lean_dec_ref(v_subst_3214_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_fvarId_3216_; lean_object* v___x_3217_; 
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
v_fvarId_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_fvarId_3216_);
lean_dec_ref(v___x_3215_);
lean_inc(v_fvarId_3216_);
v___x_3217_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3216_, v_a_2377_);
lean_dec(v_a_2377_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3217_, 0);
lean_dec(v_unused_3237_);
v___x_3219_ = v___x_3217_;
v_isShared_3220_ = v_isSharedCheck_3236_;
goto v_resetjp_3218_;
}
else
{
lean_dec(v___x_3217_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3236_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
uint8_t v___x_3221_; 
v___x_3221_ = l_Lean_instBEqFVarId_beq(v_fvarId_3212_, v_fvarId_3216_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3231_; 
v_isSharedCheck_3231_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_3232_);
v___x_3223_ = v_code_2375_;
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v_code_2375_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v_fvarId_3216_);
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_fvarId_3216_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3226_);
v___x_3228_ = v___x_3219_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v___x_3234_; 
lean_dec(v_fvarId_3216_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v_code_2375_);
v___x_3234_ = v___x_3219_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_code_2375_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v_fvarId_3216_);
lean_dec_ref(v_code_2375_);
v_a_3238_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3217_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3217_);
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
uint8_t v___x_3246_; lean_object* v___x_3247_; 
lean_dec_ref(v_code_2375_);
lean_dec(v_a_2377_);
v___x_3246_ = 0;
v___x_3247_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3246_, v_a_2379_, v_a_2380_, v___x_2600_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v___x_3247_;
}
}
case 6:
{
lean_object* v_type_3248_; lean_object* v___x_3249_; lean_object* v_subst_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; uint8_t v___x_3255_; 
lean_dec_ref(v___x_2600_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_a_2376_);
v_type_3248_ = lean_ctor_get(v_code_2375_, 0);
v___x_3249_ = lean_st_ref_get(v_a_2377_);
lean_dec(v_a_2377_);
v_subst_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_subst_3250_);
lean_dec(v___x_3249_);
v___x_3251_ = 0;
lean_inc_ref(v_type_3248_);
v___x_3252_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3251_, v_subst_3250_, v___x_2515_, v_type_3248_);
lean_dec_ref(v_subst_3250_);
v___x_3253_ = lean_ptr_addr(v_type_3248_);
v___x_3254_ = lean_ptr_addr(v___x_3252_);
v___x_3255_ = lean_usize_dec_eq(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3265_; 
v_isSharedCheck_3265_ = !lean_is_exclusive(v_code_2375_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v_code_2375_, 0);
lean_dec(v_unused_3266_);
v___x_3257_ = v_code_2375_;
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v_code_2375_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3252_);
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3252_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_3260_);
v___x_3262_ = v___x_2521_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v___x_3268_; 
lean_dec_ref(v___x_3252_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v_code_2375_);
v___x_3268_ = v___x_2521_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_code_2375_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
default: 
{
lean_object* v_decl_3270_; lean_object* v_k_3271_; 
lean_del_object(v___x_2521_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
v_decl_3270_ = lean_ctor_get(v_code_2375_, 0);
v_k_3271_ = lean_ctor_get(v_code_2375_, 1);
lean_inc_ref(v_k_3271_);
lean_inc_ref(v_decl_3270_);
v_decl_2524_ = v_decl_3270_;
v_k_2525_ = v_k_3271_;
v___y_2526_ = v_a_2376_;
v___y_2527_ = v_a_2377_;
v___y_2528_ = v_a_2378_;
v___y_2529_ = v_a_2379_;
v___y_2530_ = v_a_2380_;
v___y_2531_ = v___x_2600_;
v___y_2532_ = v_a_2382_;
goto v___jp_2523_;
}
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_del_object(v___x_2517_);
lean_dec_ref(v_inheritedTraceOptions_2514_);
lean_dec(v_cancelTk_x3f_2512_);
lean_dec(v_currMacroScope_2510_);
lean_dec(v_quotContext_2509_);
lean_dec(v_maxHeartbeats_2508_);
lean_dec(v_initHeartbeats_2507_);
lean_dec(v_openDecls_2506_);
lean_dec(v_currNamespace_2505_);
lean_dec(v_ref_2504_);
lean_dec(v_maxRecDepth_2503_);
lean_dec(v_currRecDepth_2502_);
lean_dec_ref(v_options_2501_);
lean_dec_ref(v_fileMap_2500_);
lean_dec_ref(v_fileName_2499_);
lean_dec(v_a_2382_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec_ref(v_code_2375_);
v_a_3275_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_2519_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_2519_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
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
}
else
{
lean_object* v___x_3298_; 
lean_dec_ref(v_code_2375_);
v___x_3298_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
return v___x_3298_;
}
v___jp_2384_:
{
if (v___y_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v_code_2375_);
v___x_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2386_);
lean_ctor_set(v___x_2388_, 1, v___y_2385_);
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
lean_ctor_set(v___x_2395_, 0, v___y_2393_);
lean_ctor_set(v___x_2395_, 1, v___y_2392_);
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
v___x_2404_ = lean_ptr_addr(v___y_2399_);
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
v___x_2407_ = lean_ptr_addr(v___y_2400_);
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
v___x_2412_ = lean_ptr_addr(v___y_2399_);
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
v___x_2415_ = lean_ptr_addr(v___y_2400_);
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
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
lean_inc_ref(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
v___x_2431_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2421_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v_fvarId_2433_; lean_object* v___x_2434_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref(v___x_2431_);
v_fvarId_2433_ = lean_ctor_get(v_decl_2423_, 0);
v___x_2434_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2433_, v___y_2425_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; uint8_t v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = lean_unbox(v_a_2435_);
lean_dec(v_a_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v___y_2424_);
lean_dec_ref(v_code_2375_);
v___x_2437_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2423_, v___y_2425_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec(v___y_2425_);
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
if (v___y_2422_ == 0)
{
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
v___y_2399_ = v_a_2432_;
v___y_2400_ = v_decl_2423_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2454_; 
lean_inc_ref(v_decl_2423_);
v___x_2454_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_dec_ref(v___x_2454_);
v___y_2399_ = v_a_2432_;
v___y_2400_ = v_decl_2423_;
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
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
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
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec_ref(v_decl_2423_);
lean_dec_ref(v_code_2375_);
return v___x_2431_;
}
}
v___jp_2471_:
{
lean_object* v___x_2482_; 
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
lean_inc_ref(v___y_2477_);
lean_inc(v___y_2476_);
lean_inc_ref(v___y_2475_);
v___x_2482_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref(v___x_2482_);
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
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___y_2472_);
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
if (v___y_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec_ref(v_code_2375_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2493_);
lean_ctor_set(v___x_2496_, 1, v___y_2494_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; 
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_code_2375_);
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_params_3308_; lean_object* v_type_3309_; lean_object* v_value_3310_; lean_object* v___x_3311_; lean_object* v_subst_3312_; uint8_t v___x_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_params_3308_ = lean_ctor_get(v_decl_3299_, 2);
v_type_3309_ = lean_ctor_get(v_decl_3299_, 3);
v_value_3310_ = lean_ctor_get(v_decl_3299_, 4);
v___x_3311_ = lean_st_ref_get(v_a_3301_);
v_subst_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc_ref(v_subst_3312_);
lean_dec(v___x_3311_);
v___x_3313_ = 0;
v___x_3314_ = 0;
lean_inc_ref(v_type_3309_);
v___x_3315_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3313_, v_subst_3312_, v___x_3314_, v_type_3309_);
lean_dec_ref(v_subst_3312_);
lean_inc_ref(v_params_3308_);
v___x_3316_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3313_, v___x_3314_, v_params_3308_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
lean_inc(v_a_3304_);
lean_inc_ref(v_value_3310_);
v___x_3318_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3310_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref(v___x_3318_);
v___x_3320_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3313_, v_decl_3299_, v___x_3315_, v_a_3317_, v_a_3319_, v_a_3304_);
lean_dec(v_a_3304_);
return v___x_3320_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_a_3317_);
lean_dec_ref(v___x_3315_);
lean_dec(v_a_3304_);
lean_dec_ref(v_decl_3299_);
v_a_3321_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3318_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3318_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___x_3315_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec_ref(v_decl_3299_);
v_a_3329_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3316_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3316_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3347_, lean_object* v___x_3348_, lean_object* v___x_3349_, lean_object* v_i_3350_, lean_object* v_as_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3347_, v___x_3348_, v___x_3349_, v_i_3350_, v_as_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___x_3349_);
lean_dec(v___x_3348_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3371_, lean_object* v_k_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3371_, v_k_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3392_, uint8_t v_t_3393_, lean_object* v_decl_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3392_, v_t_3393_, v_decl_3394_, v___y_3396_, v___y_3399_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3404_, lean_object* v_t_3405_, lean_object* v_decl_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v_pu_boxed_3415_; uint8_t v_t_boxed_3416_; lean_object* v_res_3417_; 
v_pu_boxed_3415_ = lean_unbox(v_pu_3404_);
v_t_boxed_3416_ = lean_unbox(v_t_3405_);
v_res_3417_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3415_, v_t_boxed_3416_, v_decl_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3418_, uint8_t v_t_3419_, lean_object* v_args_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3418_, v_t_3419_, v_args_3420_, v___y_3422_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3430_, lean_object* v_t_3431_, lean_object* v_args_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v_pu_boxed_3441_; uint8_t v_t_boxed_3442_; lean_object* v_res_3443_; 
v_pu_boxed_3441_ = lean_unbox(v_pu_3430_);
v_t_boxed_3442_ = lean_unbox(v_t_3431_);
v_res_3443_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3441_, v_t_boxed_3442_, v_args_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3444_, lean_object* v_R_3445_, lean_object* v_a_3446_, lean_object* v_b_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3446_, v_b_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_, lean_object* v_x_3452_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3450_, v_x_3451_, v_x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3454_, size_t v_i_3455_, size_t v_stop_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3454_, v_i_3455_, v_stop_3456_, v_b_3457_, v___y_3459_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3467_, lean_object* v_i_3468_, lean_object* v_stop_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
size_t v_i_boxed_3479_; size_t v_stop_boxed_3480_; lean_object* v_res_3481_; 
v_i_boxed_3479_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_stop_boxed_3480_ = lean_unbox_usize(v_stop_3469_);
lean_dec(v_stop_3469_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3467_, v_i_boxed_3479_, v_stop_boxed_3480_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v_as_3467_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3482_, size_t v_i_3483_, size_t v_stop_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3482_, v_i_3483_, v_stop_3484_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3494_, lean_object* v_i_3495_, lean_object* v_stop_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
size_t v_i_boxed_3505_; size_t v_stop_boxed_3506_; lean_object* v_res_3507_; 
v_i_boxed_3505_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_stop_boxed_3506_ = lean_unbox_usize(v_stop_3496_);
lean_dec(v_stop_3496_);
v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3494_, v_i_boxed_3505_, v_stop_boxed_3506_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_as_3494_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3508_, size_t v_i_3509_, size_t v_stop_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3508_, v_i_3509_, v_stop_3510_, v_b_3511_, v___y_3513_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3518_, lean_object* v_i_3519_, lean_object* v_stop_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
size_t v_i_boxed_3527_; size_t v_stop_boxed_3528_; lean_object* v_res_3529_; 
v_i_boxed_3527_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_stop_boxed_3528_ = lean_unbox_usize(v_stop_3520_);
lean_dec(v_stop_3520_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3518_, v_i_boxed_3527_, v_stop_boxed_3528_, v_b_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v_as_3518_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3530_, size_t v_i_3531_, size_t v_stop_3532_, lean_object* v_b_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3530_, v_i_3531_, v_stop_3532_, v_b_3533_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3543_, lean_object* v_i_3544_, lean_object* v_stop_3545_, lean_object* v_b_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
size_t v_i_boxed_3555_; size_t v_stop_boxed_3556_; lean_object* v_res_3557_; 
v_i_boxed_3555_ = lean_unbox_usize(v_i_3544_);
lean_dec(v_i_3544_);
v_stop_boxed_3556_ = lean_unbox_usize(v_stop_3545_);
lean_dec(v_stop_3545_);
v_res_3557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3543_, v_i_boxed_3555_, v_stop_boxed_3556_, v_b_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_as_3543_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3558_, size_t v_i_3559_, size_t v_stop_3560_, lean_object* v_b_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3558_, v_i_3559_, v_stop_3560_, v_b_3561_, v___y_3566_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3571_, lean_object* v_i_3572_, lean_object* v_stop_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
size_t v_i_boxed_3583_; size_t v_stop_boxed_3584_; lean_object* v_res_3585_; 
v_i_boxed_3583_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_stop_boxed_3584_ = lean_unbox_usize(v_stop_3573_);
lean_dec(v_stop_3573_);
v_res_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3571_, v_i_boxed_3583_, v_stop_boxed_3584_, v_b_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v_as_3571_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3586_, size_t v_i_3587_, size_t v_stop_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3586_, v_i_3587_, v_stop_3588_, v___y_3590_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3598_, lean_object* v_i_3599_, lean_object* v_stop_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
size_t v_i_boxed_3609_; size_t v_stop_boxed_3610_; lean_object* v_res_3611_; 
v_i_boxed_3609_ = lean_unbox_usize(v_i_3599_);
lean_dec(v_i_3599_);
v_stop_boxed_3610_ = lean_unbox_usize(v_stop_3600_);
lean_dec(v_stop_3600_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3598_, v_i_boxed_3609_, v_stop_boxed_3610_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v_as_3598_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3612_, size_t v_sz_3613_, size_t v_i_3614_, lean_object* v_b_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3612_, v_sz_3613_, v_i_3614_, v_b_3615_, v___y_3617_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3625_, lean_object* v_sz_3626_, lean_object* v_i_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3626_);
lean_dec(v_sz_3626_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3627_);
lean_dec(v_i_3627_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3625_, v_sz_boxed_3637_, v_i_boxed_3638_, v_b_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_as_3625_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3640_, lean_object* v_x_3641_, size_t v_x_3642_, size_t v_x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3641_, v_x_3642_, v_x_3643_, v_x_3644_, v_x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_, lean_object* v_x_3652_){
_start:
{
size_t v_x_49521__boxed_3653_; size_t v_x_49522__boxed_3654_; lean_object* v_res_3655_; 
v_x_49521__boxed_3653_ = lean_unbox_usize(v_x_3649_);
lean_dec(v_x_3649_);
v_x_49522__boxed_3654_ = lean_unbox_usize(v_x_3650_);
lean_dec(v_x_3650_);
v_res_3655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3647_, v_x_3648_, v_x_49521__boxed_3653_, v_x_49522__boxed_3654_, v_x_3651_, v_x_3652_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3656_, uint8_t v_t_3657_, lean_object* v_i_3658_, lean_object* v_as_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3656_, v_t_3657_, v_i_3658_, v_as_3659_, v___y_3661_, v___y_3664_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3669_, lean_object* v_t_3670_, lean_object* v_i_3671_, lean_object* v_as_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
uint8_t v_pu_boxed_3681_; uint8_t v_t_boxed_3682_; lean_object* v_res_3683_; 
v_pu_boxed_3681_ = lean_unbox(v_pu_3669_);
v_t_boxed_3682_ = lean_unbox(v_t_3670_);
v_res_3683_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3681_, v_t_boxed_3682_, v_i_3671_, v_as_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3684_, lean_object* v_n_3685_, lean_object* v_k_3686_, lean_object* v_v_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3685_, v_k_3686_, v_v_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3689_, size_t v_depth_3690_, lean_object* v_keys_3691_, lean_object* v_vals_3692_, lean_object* v_heq_3693_, lean_object* v_i_3694_, lean_object* v_entries_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3690_, v_keys_3691_, v_vals_3692_, v_i_3694_, v_entries_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3697_, lean_object* v_depth_3698_, lean_object* v_keys_3699_, lean_object* v_vals_3700_, lean_object* v_heq_3701_, lean_object* v_i_3702_, lean_object* v_entries_3703_){
_start:
{
size_t v_depth_boxed_3704_; lean_object* v_res_3705_; 
v_depth_boxed_3704_ = lean_unbox_usize(v_depth_3698_);
lean_dec(v_depth_3698_);
v_res_3705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3697_, v_depth_boxed_3704_, v_keys_3699_, v_vals_3700_, v_heq_3701_, v_i_3702_, v_entries_3703_);
lean_dec_ref(v_vals_3700_);
lean_dec_ref(v_keys_3699_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3707_, v_x_3708_, v_x_3709_, v_x_3710_);
return v___x_3711_;
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
