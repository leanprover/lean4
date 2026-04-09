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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_325_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_323_, v_value_297_, v_fst_321_, v___x_324_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_n(v_a_326_, 2);
lean_dec_ref(v___x_325_);
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
lean_dec_ref(v___x_692_);
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
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v___x_711_);
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
uint8_t v___x_24446__boxed_824_; size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v___x_24446__boxed_824_ = lean_unbox(v___x_820_);
v_sz_boxed_825_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_826_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24446__boxed_824_, v_sz_boxed_825_, v_i_boxed_826_, v_bs_823_);
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
lean_dec_ref(v___x_1020_);
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
lean_dec_ref(v___x_1111_);
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1167_; uint64_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1723u);
v___x_1168_ = lean_uint64_of_nat(v___x_1167_);
return v___x_1168_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; 
v___x_1169_ = ((size_t)5ULL);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_shift_left(v___x_1170_, v___x_1169_);
return v___x_1171_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; 
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
v___x_1174_ = lean_usize_sub(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* v_x_1176_, size_t v_x_1177_, size_t v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v_es_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; lean_object* v_j_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_es_1181_ = lean_ctor_get(v_x_1176_, 0);
v___x_1182_ = ((size_t)5ULL);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1);
v___x_1185_ = lean_usize_land(v_x_1177_, v___x_1184_);
v_j_1186_ = lean_usize_to_nat(v___x_1185_);
v___x_1187_ = lean_array_get_size(v_es_1181_);
v___x_1188_ = lean_nat_dec_lt(v_j_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec(v_j_1186_);
lean_dec(v_x_1180_);
lean_dec(v_x_1179_);
return v_x_1176_;
}
else
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1225_; 
lean_inc_ref(v_es_1181_);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_x_1176_, 0);
lean_dec(v_unused_1226_);
v___x_1190_ = v_x_1176_;
v_isShared_1191_ = v_isSharedCheck_1225_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_x_1176_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1225_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_v_1192_; lean_object* v___x_1193_; lean_object* v_xs_x27_1194_; lean_object* v___y_1196_; 
v_v_1192_ = lean_array_fget(v_es_1181_, v_j_1186_);
v___x_1193_ = lean_box(0);
v_xs_x27_1194_ = lean_array_fset(v_es_1181_, v_j_1186_, v___x_1193_);
switch(lean_obj_tag(v_v_1192_))
{
case 0:
{
lean_object* v_key_1201_; lean_object* v_val_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_key_1201_ = lean_ctor_get(v_v_1192_, 0);
v_val_1202_ = lean_ctor_get(v_v_1192_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_v_1192_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v_v_1192_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_val_1202_);
lean_inc(v_key_1201_);
lean_dec(v_v_1192_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_name_eq(v_x_1179_, v_key_1201_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_del_object(v___x_1204_);
v___x_1207_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1201_, v_val_1202_, v_x_1179_, v_x_1180_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___y_1196_ = v___x_1208_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1210_; 
lean_dec(v_val_1202_);
lean_dec(v_key_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_x_1180_);
lean_ctor_set(v___x_1204_, 0, v_x_1179_);
v___x_1210_ = v___x_1204_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_x_1179_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_x_1180_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v___y_1196_ = v___x_1210_;
goto v___jp_1195_;
}
}
}
}
case 1:
{
lean_object* v_node_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_node_1213_ = lean_ctor_get(v_v_1192_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_v_1192_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1215_ = v_v_1192_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_node_1213_);
lean_dec(v_v_1192_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1217_ = lean_usize_shift_right(v_x_1177_, v___x_1182_);
v___x_1218_ = lean_usize_add(v_x_1178_, v___x_1183_);
v___x_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_1213_, v___x_1217_, v___x_1218_, v_x_1179_, v_x_1180_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1219_);
v___x_1221_ = v___x_1215_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1196_ = v___x_1221_;
goto v___jp_1195_;
}
}
}
default: 
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_x_1179_);
lean_ctor_set(v___x_1224_, 1, v_x_1180_);
v___y_1196_ = v___x_1224_;
goto v___jp_1195_;
}
}
v___jp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_array_fset(v_xs_x27_1194_, v_j_1186_, v___y_1196_);
lean_dec(v_j_1186_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1197_);
v___x_1199_ = v___x_1190_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_ks_1227_; lean_object* v_vs_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1248_; 
v_ks_1227_ = lean_ctor_get(v_x_1176_, 0);
v_vs_1228_ = lean_ctor_get(v_x_1176_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1230_ = v_x_1176_;
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_vs_1228_);
lean_inc(v_ks_1227_);
lean_dec(v_x_1176_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ks_1227_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_vs_1228_);
v___x_1233_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v_newNode_1234_; uint8_t v___y_1236_; size_t v___x_1242_; uint8_t v___x_1243_; 
v_newNode_1234_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_1233_, v_x_1179_, v_x_1180_);
v___x_1242_ = ((size_t)7ULL);
v___x_1243_ = lean_usize_dec_le(v___x_1242_, v_x_1178_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1234_);
v___x_1245_ = lean_unsigned_to_nat(4u);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
lean_dec(v___x_1244_);
v___y_1236_ = v___x_1246_;
goto v___jp_1235_;
}
else
{
v___y_1236_ = v___x_1243_;
goto v___jp_1235_;
}
v___jp_1235_:
{
if (v___y_1236_ == 0)
{
lean_object* v_ks_1237_; lean_object* v_vs_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_ks_1237_ = lean_ctor_get(v_newNode_1234_, 0);
lean_inc_ref(v_ks_1237_);
v_vs_1238_ = lean_ctor_get(v_newNode_1234_, 1);
lean_inc_ref(v_vs_1238_);
lean_dec_ref(v_newNode_1234_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2);
v___x_1241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_1178_, v_ks_1237_, v_vs_1238_, v___x_1239_, v___x_1240_);
lean_dec_ref(v_vs_1238_);
lean_dec_ref(v_ks_1237_);
return v___x_1241_;
}
else
{
return v_newNode_1234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t v_depth_1249_, lean_object* v_keys_1250_, lean_object* v_vals_1251_, lean_object* v_i_1252_, lean_object* v_entries_1253_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_keys_1250_);
v___x_1255_ = lean_nat_dec_lt(v_i_1252_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_i_1252_);
return v_entries_1253_;
}
else
{
lean_object* v_k_1256_; lean_object* v_v_1257_; uint64_t v___y_1259_; 
v_k_1256_ = lean_array_fget_borrowed(v_keys_1250_, v_i_1252_);
v_v_1257_ = lean_array_fget_borrowed(v_vals_1251_, v_i_1252_);
if (lean_obj_tag(v_k_1256_) == 0)
{
uint64_t v___x_1270_; 
v___x_1270_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1259_ = v___x_1270_;
goto v___jp_1258_;
}
else
{
uint64_t v_hash_1271_; 
v_hash_1271_ = lean_ctor_get_uint64(v_k_1256_, sizeof(void*)*2);
v___y_1259_ = v_hash_1271_;
goto v___jp_1258_;
}
v___jp_1258_:
{
size_t v_h_1260_; size_t v___x_1261_; lean_object* v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; size_t v_h_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_h_1260_ = lean_uint64_to_usize(v___y_1259_);
v___x_1261_ = ((size_t)5ULL);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_sub(v_depth_1249_, v___x_1263_);
v___x_1265_ = lean_usize_mul(v___x_1261_, v___x_1264_);
v_h_1266_ = lean_usize_shift_right(v_h_1260_, v___x_1265_);
v___x_1267_ = lean_nat_add(v_i_1252_, v___x_1262_);
lean_dec(v_i_1252_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
v___x_1268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_1253_, v_h_1266_, v_depth_1249_, v_k_1256_, v_v_1257_);
v_i_1252_ = v___x_1267_;
v_entries_1253_ = v___x_1268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_depth_1272_, lean_object* v_keys_1273_, lean_object* v_vals_1274_, lean_object* v_i_1275_, lean_object* v_entries_1276_){
_start:
{
size_t v_depth_boxed_1277_; lean_object* v_res_1278_; 
v_depth_boxed_1277_ = lean_unbox_usize(v_depth_1272_);
lean_dec(v_depth_1272_);
v_res_1278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_1277_, v_keys_1273_, v_vals_1274_, v_i_1275_, v_entries_1276_);
lean_dec_ref(v_vals_1274_);
lean_dec_ref(v_keys_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
size_t v_x_44817__boxed_1284_; size_t v_x_44818__boxed_1285_; lean_object* v_res_1286_; 
v_x_44817__boxed_1284_ = lean_unbox_usize(v_x_1280_);
lean_dec(v_x_1280_);
v_x_44818__boxed_1285_ = lean_unbox_usize(v_x_1281_);
lean_dec(v_x_1281_);
v_res_1286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1279_, v_x_44817__boxed_1284_, v_x_44818__boxed_1285_, v_x_1282_, v_x_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint64_t v___y_1291_; 
if (lean_obj_tag(v_x_1288_) == 0)
{
uint64_t v___x_1295_; 
v___x_1295_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
v___y_1291_ = v___x_1295_;
goto v___jp_1290_;
}
else
{
uint64_t v_hash_1296_; 
v_hash_1296_ = lean_ctor_get_uint64(v_x_1288_, sizeof(void*)*2);
v___y_1291_ = v_hash_1296_;
goto v___jp_1290_;
}
v___jp_1290_:
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_uint64_to_usize(v___y_1291_);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1287_, v___x_1292_, v___x_1293_, v_x_1288_, v_x_1289_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* v_a_1297_, lean_object* v_b_1298_){
_start:
{
lean_object* v_array_1299_; lean_object* v_start_1300_; lean_object* v_stop_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1314_; 
v_array_1299_ = lean_ctor_get(v_a_1297_, 0);
v_start_1300_ = lean_ctor_get(v_a_1297_, 1);
v_stop_1301_ = lean_ctor_get(v_a_1297_, 2);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1303_ = v_a_1297_;
v_isShared_1304_ = v_isSharedCheck_1314_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_stop_1301_);
lean_inc(v_start_1300_);
lean_inc(v_array_1299_);
lean_dec(v_a_1297_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1314_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_nat_dec_lt(v_start_1300_, v_stop_1301_);
if (v___x_1305_ == 0)
{
lean_del_object(v___x_1303_);
lean_dec(v_stop_1301_);
lean_dec(v_start_1300_);
lean_dec_ref(v_array_1299_);
return v_b_1298_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v_start_1300_, v___x_1306_);
lean_inc_ref(v_array_1299_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v___x_1307_);
v___x_1309_ = v___x_1303_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_array_1299_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_stop_1301_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_array_fget(v_array_1299_, v_start_1300_);
lean_dec(v_start_1300_);
lean_dec_ref(v_array_1299_);
v___x_1311_ = lean_array_push(v_b_1298_, v___x_1310_);
v_a_1297_ = v___x_1309_;
v_b_1298_ = v___x_1311_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* v_as_1315_, size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_b_1318_);
return v___x_1322_;
}
else
{
lean_object* v_array_1323_; lean_object* v_start_1324_; lean_object* v_stop_1325_; uint8_t v___x_1326_; 
v_array_1323_ = lean_ctor_get(v_b_1318_, 0);
v_start_1324_ = lean_ctor_get(v_b_1318_, 1);
v_stop_1325_ = lean_ctor_get(v_b_1318_, 2);
v___x_1326_ = lean_nat_dec_lt(v_start_1324_, v_stop_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1318_);
return v___x_1327_;
}
else
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1360_; 
lean_inc(v_stop_1325_);
lean_inc(v_start_1324_);
lean_inc_ref(v_array_1323_);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_b_1318_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1361_ = lean_ctor_get(v_b_1318_, 2);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_b_1318_, 1);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_b_1318_, 0);
lean_dec(v_unused_1363_);
v___x_1329_ = v_b_1318_;
v_isShared_1330_ = v_isSharedCheck_1360_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v_b_1318_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1360_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v_fvarId_1333_; lean_object* v_subst_1334_; lean_object* v_used_1335_; lean_object* v_binderRenaming_1336_; lean_object* v_funDeclInfoMap_1337_; uint8_t v_simplified_1338_; lean_object* v_visited_1339_; lean_object* v_inline_1340_; lean_object* v_inlineLocal_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1359_; 
v___x_1331_ = lean_st_ref_take(v___y_1319_);
v_a_1332_ = lean_array_uget_borrowed(v_as_1315_, v_i_1317_);
v_fvarId_1333_ = lean_ctor_get(v_a_1332_, 0);
v_subst_1334_ = lean_ctor_get(v___x_1331_, 0);
v_used_1335_ = lean_ctor_get(v___x_1331_, 1);
v_binderRenaming_1336_ = lean_ctor_get(v___x_1331_, 2);
v_funDeclInfoMap_1337_ = lean_ctor_get(v___x_1331_, 3);
v_simplified_1338_ = lean_ctor_get_uint8(v___x_1331_, sizeof(void*)*7);
v_visited_1339_ = lean_ctor_get(v___x_1331_, 4);
v_inline_1340_ = lean_ctor_get(v___x_1331_, 5);
v_inlineLocal_1341_ = lean_ctor_get(v___x_1331_, 6);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1343_ = v___x_1331_;
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_inlineLocal_1341_);
lean_inc(v_inline_1340_);
lean_inc(v_visited_1339_);
lean_inc(v_funDeclInfoMap_1337_);
lean_inc(v_binderRenaming_1336_);
lean_inc(v_used_1335_);
lean_inc(v_subst_1334_);
lean_dec(v___x_1331_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1345_ = lean_array_fget_borrowed(v_array_1323_, v_start_1324_);
lean_inc(v___x_1345_);
lean_inc(v_fvarId_1333_);
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_1334_, v_fvarId_1333_, v___x_1345_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1346_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_used_1335_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_binderRenaming_1336_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_funDeclInfoMap_1337_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_visited_1339_);
lean_ctor_set(v_reuseFailAlloc_1358_, 5, v_inline_1340_);
lean_ctor_set(v_reuseFailAlloc_1358_, 6, v_inlineLocal_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*7, v_simplified_1338_);
v___x_1348_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1349_ = lean_st_ref_set(v___y_1319_, v___x_1348_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_add(v_start_1324_, v___x_1350_);
lean_dec(v_start_1324_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v___x_1351_);
v___x_1353_ = v___x_1329_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_array_1323_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_stop_1325_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
size_t v___x_1354_; size_t v___x_1355_; 
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_add(v_i_1317_, v___x_1354_);
v_i_1317_ = v___x_1355_;
v_b_1318_ = v___x_1353_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* v_as_1364_, lean_object* v_sz_1365_, lean_object* v_i_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
size_t v_sz_boxed_1370_; size_t v_i_boxed_1371_; lean_object* v_res_1372_; 
v_sz_boxed_1370_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1371_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_1364_, v_sz_boxed_1370_, v_i_boxed_1371_, v_b_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v_as_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* v_as_1373_, size_t v_i_1374_, size_t v_stop_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_usize_dec_eq(v_i_1374_, v_stop_1375_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = 0;
v___x_1381_ = lean_array_uget_borrowed(v_as_1373_, v_i_1374_);
v___x_1382_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1380_, v___x_1381_, v___y_1377_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; size_t v___x_1384_; size_t v___x_1385_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_add(v_i_1374_, v___x_1384_);
v_i_1374_ = v___x_1385_;
v_b_1376_ = v_a_1383_;
goto _start;
}
else
{
return v___x_1382_;
}
}
else
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_b_1376_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* v_as_1388_, lean_object* v_i_1389_, lean_object* v_stop_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
size_t v_i_boxed_1394_; size_t v_stop_boxed_1395_; lean_object* v_res_1396_; 
v_i_boxed_1394_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_stop_boxed_1395_ = lean_unbox_usize(v_stop_1390_);
lean_dec(v_stop_1390_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_1388_, v_i_boxed_1394_, v_stop_boxed_1395_, v_b_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v_as_1388_);
return v_res_1396_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = 0;
v___x_1398_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* v_msg_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
v___x_1401_ = lean_panic_fn_borrowed(v___x_1400_, v_msg_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* v_as_1402_, size_t v_i_1403_, size_t v_stop_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_eq(v_i_1403_, v_stop_1404_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v_type_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_array_uget_borrowed(v_as_1402_, v_i_1403_);
v_type_1409_ = lean_ctor_get(v___x_1408_, 2);
v___x_1410_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(v_type_1409_, v___y_1405_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1422_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1422_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_unbox(v_a_1411_);
if (v___x_1415_ == 0)
{
size_t v___x_1416_; size_t v___x_1417_; 
lean_del_object(v___x_1413_);
lean_dec(v_a_1411_);
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1403_, v___x_1416_);
v_i_1403_ = v___x_1417_;
goto _start;
}
else
{
lean_object* v___x_1420_; 
if (v_isShared_1414_ == 0)
{
v___x_1420_ = v___x_1413_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1411_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
return v___x_1410_;
}
}
else
{
uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = 0;
v___x_1424_ = lean_box(v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* v_as_1426_, lean_object* v_i_1427_, lean_object* v_stop_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
size_t v_i_boxed_1431_; size_t v_stop_boxed_1432_; lean_object* v_res_1433_; 
v_i_boxed_1431_ = lean_unbox_usize(v_i_1427_);
lean_dec(v_i_1427_);
v_stop_boxed_1432_ = lean_unbox_usize(v_stop_1428_);
lean_dec(v_stop_1428_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_1426_, v_i_boxed_1431_, v_stop_boxed_1432_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v_as_1426_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* v_as_1434_, size_t v_i_1435_, size_t v_stop_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_eq(v_i_1435_, v_stop_1436_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = 0;
v___x_1442_ = lean_array_uget_borrowed(v_as_1434_, v_i_1435_);
v___x_1443_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_1441_, v___x_1442_, v___y_1438_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; size_t v___x_1445_; size_t v___x_1446_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_add(v_i_1435_, v___x_1445_);
v_i_1435_ = v___x_1446_;
v_b_1437_ = v_a_1444_;
goto _start;
}
else
{
return v___x_1443_;
}
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1437_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* v_as_1449_, lean_object* v_i_1450_, lean_object* v_stop_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
size_t v_i_boxed_1455_; size_t v_stop_boxed_1456_; lean_object* v_res_1457_; 
v_i_boxed_1455_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_stop_boxed_1456_ = lean_unbox_usize(v_stop_1451_);
lean_dec(v_stop_1451_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_1449_, v_i_boxed_1455_, v_stop_boxed_1456_, v_b_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v_as_1449_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_a_1468_; lean_object* v___y_1473_; uint8_t v___x_1475_; 
v___x_1475_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_uget_borrowed(v_as_1458_, v_i_1459_);
v___x_1478_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_1477_);
v___x_1479_ = lean_array_get_size(v___x_1478_);
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_nat_dec_lt(v___x_1476_, v___x_1479_);
if (v___x_1481_ == 0)
{
lean_dec_ref(v___x_1478_);
v_a_1468_ = v___x_1480_;
goto v___jp_1467_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_nat_dec_le(v___x_1479_, v___x_1479_);
if (v___x_1482_ == 0)
{
if (v___x_1481_ == 0)
{
lean_dec_ref(v___x_1478_);
v_a_1468_ = v___x_1480_;
goto v___jp_1467_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1479_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1478_, v___x_1483_, v___x_1484_, v___x_1480_, v___y_1463_);
lean_dec_ref(v___x_1478_);
v___y_1473_ = v___x_1485_;
goto v___jp_1472_;
}
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1479_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_1478_, v___x_1486_, v___x_1487_, v___x_1480_, v___y_1463_);
lean_dec_ref(v___x_1478_);
v___y_1473_ = v___x_1488_;
goto v___jp_1472_;
}
}
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_b_1461_);
return v___x_1489_;
}
v___jp_1467_:
{
size_t v___x_1469_; size_t v___x_1470_; 
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_add(v_i_1459_, v___x_1469_);
v_i_1459_ = v___x_1470_;
v_b_1461_ = v_a_1468_;
goto _start;
}
v___jp_1472_:
{
if (lean_obj_tag(v___y_1473_) == 0)
{
lean_object* v_a_1474_; 
v_a_1474_ = lean_ctor_get(v___y_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___y_1473_);
v_a_1468_ = v_a_1474_;
goto v___jp_1467_;
}
else
{
return v___y_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* v_as_1490_, lean_object* v_i_1491_, lean_object* v_stop_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
size_t v_i_boxed_1499_; size_t v_stop_boxed_1500_; lean_object* v_res_1501_; 
v_i_boxed_1499_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_stop_boxed_1500_ = lean_unbox_usize(v_stop_1492_);
lean_dec(v_stop_1492_);
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_1490_, v_i_boxed_1499_, v_stop_boxed_1500_, v_b_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v_as_1490_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* v_as_1502_, size_t v_i_1503_, size_t v_stop_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_eq(v_i_1503_, v_stop_1504_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v_fvarId_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_array_uget_borrowed(v_as_1502_, v_i_1503_);
v_fvarId_1509_ = lean_ctor_get(v___x_1508_, 0);
v___x_1510_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1509_, v___y_1505_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1522_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1522_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1522_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_unbox(v_a_1511_);
if (v___x_1515_ == 0)
{
size_t v___x_1516_; size_t v___x_1517_; 
lean_del_object(v___x_1513_);
lean_dec(v_a_1511_);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1503_, v___x_1516_);
v_i_1503_ = v___x_1517_;
goto _start;
}
else
{
lean_object* v___x_1520_; 
if (v_isShared_1514_ == 0)
{
v___x_1520_ = v___x_1513_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1511_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
return v___x_1510_;
}
}
else
{
uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = 0;
v___x_1524_ = lean_box(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* v_as_1526_, lean_object* v_i_1527_, lean_object* v_stop_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
size_t v_i_boxed_1531_; size_t v_stop_boxed_1532_; lean_object* v_res_1533_; 
v_i_boxed_1531_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_stop_boxed_1532_ = lean_unbox_usize(v_stop_1528_);
lean_dec(v_stop_1528_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_1526_, v_i_boxed_1531_, v_stop_boxed_1532_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v_as_1526_);
return v_res_1533_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1537_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
v___x_1538_ = lean_unsigned_to_nat(9u);
v___x_1539_ = lean_unsigned_to_nat(640u);
v___x_1540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
v___x_1541_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
v___x_1542_ = l_mkPanicMessageWithDecl(v___x_1541_, v___x_1540_, v___x_1539_, v___x_1538_, v___x_1537_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v_fvarId_1548_, lean_object* v_k_1549_, lean_object* v_args_1550_, uint8_t v___x_1551_, lean_object* v___x_1552_, lean_object* v_result_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_lower_1563_; lean_object* v_upper_1564_; uint8_t v___x_1591_; 
v___x_1591_ = lean_nat_dec_lt(v___x_1546_, v___x_1547_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_dec(v___x_1552_);
lean_dec_ref(v_args_1550_);
lean_dec(v___x_1547_);
lean_dec(v___x_1546_);
v___x_1592_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1548_, v_result_1553_, v___y_1555_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; 
lean_dec_ref(v___x_1592_);
lean_inc_ref(v___y_1559_);
v___x_1593_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1549_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1593_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_k_1549_);
v_a_1594_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1592_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1592_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_le(v___x_1546_, v___x_1552_);
if (v___x_1602_ == 0)
{
lean_dec(v___x_1552_);
v_lower_1563_ = v___x_1546_;
v_upper_1564_ = v___x_1547_;
goto v___jp_1562_;
}
else
{
lean_dec(v___x_1546_);
v_lower_1563_ = v___x_1552_;
v_upper_1564_ = v___x_1547_;
goto v___jp_1562_;
}
}
v___jp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1565_ = l_Array_toSubarray___redArg(v_args_1550_, v_lower_1563_, v_upper_1564_);
v___x_1566_ = l_Subarray_copy___redArg(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_result_1553_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_1569_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1551_, v___x_1567_, v___x_1568_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_fvarId_1571_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v_fvarId_1571_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_fvarId_1571_);
v___x_1572_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1548_, v_fvarId_1571_, v___y_1555_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v___x_1572_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1570_);
lean_ctor_set(v___x_1573_, 1, v_k_1549_);
lean_inc_ref(v___y_1559_);
v___x_1574_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1573_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1570_);
lean_dec_ref(v_k_1549_);
v_a_1575_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1572_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1572_);
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
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_k_1549_);
lean_dec(v_fvarId_1548_);
v_a_1583_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1569_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1569_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v_fvarId_1605_, lean_object* v_k_1606_, lean_object* v_args_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_result_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v___x_45347__boxed_1619_; lean_object* v_res_1620_; 
v___x_45347__boxed_1619_ = lean_unbox(v___x_1608_);
v_res_1620_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1603_, v___x_1604_, v_fvarId_1605_, v_k_1606_, v_args_1607_, v___x_45347__boxed_1619_, v___x_1609_, v_result_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1621_, lean_object* v_k_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_fvarId_1631_; lean_object* v_value_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1970_; 
v_fvarId_1631_ = lean_ctor_get(v_letDecl_1621_, 0);
v_value_1632_ = lean_ctor_get(v_letDecl_1621_, 3);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_letDecl_1621_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; lean_object* v_unused_1972_; 
v_unused_1971_ = lean_ctor_get(v_letDecl_1621_, 2);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_letDecl_1621_, 1);
lean_dec(v_unused_1972_);
v___x_1634_ = v_letDecl_1621_;
v_isShared_1635_ = v_isSharedCheck_1970_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_value_1632_);
lean_inc(v_fvarId_1631_);
lean_dec(v_letDecl_1621_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1970_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; 
lean_inc(v_value_1632_);
v___x_1636_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1632_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1961_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1961_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1961_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
if (lean_obj_tag(v_a_1637_) == 1)
{
lean_object* v_val_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1956_; 
lean_del_object(v___x_1639_);
v_val_1641_ = lean_ctor_get(v_a_1637_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1643_ = v_a_1637_;
v_isShared_1644_ = v_isSharedCheck_1956_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_val_1641_);
lean_dec(v_a_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1956_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_params_1645_; lean_object* v_value_1646_; lean_object* v_fType_1647_; lean_object* v_args_1648_; uint8_t v_recursive_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; 
v_params_1645_ = lean_ctor_get(v_val_1641_, 0);
v_value_1646_ = lean_ctor_get(v_val_1641_, 1);
v_fType_1647_ = lean_ctor_get(v_val_1641_, 2);
v_args_1648_ = lean_ctor_get(v_val_1641_, 3);
v_recursive_1649_ = lean_ctor_get_uint8(v_val_1641_, sizeof(void*)*4 + 2);
v___x_1650_ = lean_array_get_size(v_args_1648_);
v___x_1651_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1641_);
v___x_1652_ = lean_nat_dec_lt(v___x_1650_, v___x_1651_);
if (lean_obj_tag(v_value_1632_) == 3)
{
lean_object* v_declName_1936_; lean_object* v___x_1937_; 
v_declName_1936_ = lean_ctor_get(v_value_1632_, 0);
lean_inc_n(v_declName_1936_, 2);
lean_dec_ref(v_value_1632_);
v___x_1937_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1649_, v_declName_1936_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_declName_1939_; lean_object* v_config_1940_; lean_object* v_inlineStack_1941_; lean_object* v_inlineStackOccs_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v_declName_1939_ = lean_ctor_get(v_a_1623_, 0);
v_config_1940_ = lean_ctor_get(v_a_1623_, 1);
v_inlineStack_1941_ = lean_ctor_get(v_a_1623_, 2);
v_inlineStackOccs_1942_ = lean_ctor_get(v_a_1623_, 3);
lean_inc(v_inlineStack_1941_);
lean_inc(v_declName_1936_);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_declName_1936_);
lean_ctor_set(v___x_1943_, 1, v_inlineStack_1941_);
lean_inc_ref(v_inlineStackOccs_1942_);
v___x_1944_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1942_, v_declName_1936_, v_a_1938_);
lean_inc_ref(v_config_1940_);
lean_inc(v_declName_1939_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 3, v___x_1944_);
lean_ctor_set(v___x_1634_, 2, v___x_1943_);
lean_ctor_set(v___x_1634_, 1, v_config_1940_);
lean_ctor_set(v___x_1634_, 0, v_declName_1939_);
v___x_1946_ = v___x_1634_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_declName_1939_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_config_1940_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
v___y_1835_ = v___x_1946_;
v___y_1836_ = v_a_1624_;
v___y_1837_ = v_a_1625_;
v___y_1838_ = v_a_1626_;
v___y_1839_ = v_a_1627_;
v___y_1840_ = v_a_1628_;
v___y_1841_ = v_a_1629_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_declName_1936_);
lean_dec(v___x_1651_);
lean_del_object(v___x_1643_);
lean_dec(v_val_1641_);
lean_del_object(v___x_1634_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
v_a_1948_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1937_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1937_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_del_object(v___x_1634_);
lean_dec(v_value_1632_);
lean_inc_ref(v_a_1623_);
v___y_1835_ = v_a_1623_;
v___y_1836_ = v_a_1624_;
v___y_1837_ = v_a_1625_;
v___y_1838_ = v_a_1626_;
v___y_1839_ = v_a_1627_;
v___y_1840_ = v_a_1628_;
v___y_1841_ = v_a_1629_;
goto v___jp_1834_;
}
v___jp_1653_:
{
lean_object* v___x_1667_; 
lean_inc_ref(v___y_1664_);
v___x_1667_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1656_, v___y_1654_, v___y_1657_, v___y_1661_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1657_);
if (lean_obj_tag(v___x_1669_) == 0)
{
uint8_t v___x_1670_; 
lean_dec_ref(v___x_1669_);
v___x_1670_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1668_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec_ref(v___y_1659_);
v___x_1671_ = lean_mk_empty_array_with_capacity(v___y_1665_);
lean_dec(v___y_1665_);
lean_inc_ref(v___x_1671_);
v___x_1672_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1655_, v___x_1671_);
v___x_1673_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1663_, v_fType_1647_, v___x_1672_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_n(v_a_1674_, 2);
lean_dec_ref(v___x_1673_);
v___x_1675_ = l_Lean_Expr_headBeta(v_a_1674_);
v___x_1676_ = l_Lean_Expr_isForall(v___x_1675_);
lean_dec_ref(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v___x_1671_);
v___x_1677_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1663_, v_a_1674_, v___x_1652_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_fvarId_1679_; lean_object* v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
v_fvarId_1679_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1660_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1657_);
lean_inc(v_fvarId_1679_);
v___x_1680_ = lean_apply_9(v___y_1658_, v_fvarId_1679_, v___y_1654_, v___y_1657_, v___y_1661_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_, lean_box(0));
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_mk_empty_array_with_capacity(v___x_1682_);
v___x_1684_ = lean_array_push(v___x_1683_, v_a_1678_);
v___x_1685_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1686_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1663_, v___x_1684_, v_a_1681_, v___x_1685_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc_n(v_a_1687_, 2);
lean_dec_ref(v___x_1686_);
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1688_, 0, v_a_1687_);
lean_closure_set(v___f_1688_, 1, v___x_1682_);
v___x_1689_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1663_, v_a_1668_, v___f_1688_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1701_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1687_);
lean_ctor_set(v___x_1694_, 1, v_a_1690_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1694_);
v___x_1696_ = v___x_1643_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1696_);
v___x_1698_ = v___x_1692_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1687_);
lean_del_object(v___x_1643_);
v_a_1702_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1689_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1689_);
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
lean_dec(v_a_1668_);
lean_del_object(v___x_1643_);
v_a_1710_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1686_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1686_);
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
lean_dec(v_a_1678_);
lean_dec(v_a_1668_);
lean_del_object(v___x_1643_);
v_a_1718_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1680_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1680_);
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
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_a_1668_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1654_);
lean_del_object(v___x_1643_);
v_a_1726_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1677_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1677_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v_a_1674_);
v___x_1734_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1735_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1671_, v_a_1668_, v___x_1734_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1736_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v_fvarId_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v_fvarId_1739_ = lean_ctor_get(v_a_1738_, 0);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1660_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1654_);
lean_inc(v_fvarId_1739_);
v___x_1740_ = lean_apply_9(v___y_1658_, v_fvarId_1739_, v___y_1654_, v___y_1657_, v___y_1661_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_, lean_box(0));
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_a_1738_);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_mk_empty_array_with_capacity(v___x_1743_);
v___x_1745_ = lean_array_push(v___x_1744_, v___x_1742_);
v___x_1746_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1745_, v_a_1741_, v___y_1654_, v___y_1657_, v___y_1661_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___x_1745_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1757_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_a_1747_);
v___x_1752_ = v___x_1643_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1752_);
v___x_1754_ = v___x_1749_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
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
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1643_);
v_a_1758_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1746_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1746_);
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
lean_dec(v_a_1738_);
lean_dec_ref(v___y_1654_);
lean_del_object(v___x_1643_);
v_a_1766_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1740_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1740_);
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
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1654_);
lean_del_object(v___x_1643_);
v_a_1774_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1737_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1737_);
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
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1654_);
lean_del_object(v___x_1643_);
v_a_1782_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1735_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1735_);
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
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___x_1671_);
lean_dec(v_a_1668_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1654_);
lean_del_object(v___x_1643_);
v_a_1790_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1673_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1673_);
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
else
{
lean_object* v___x_1798_; 
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_fType_1647_);
v___x_1798_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1663_, v_a_1668_, v___y_1659_, v___y_1660_, v___y_1666_, v___y_1664_, v___y_1662_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1809_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_a_1799_);
v___x_1804_ = v___x_1643_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
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
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_del_object(v___x_1643_);
v_a_1810_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1798_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1798_);
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
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1668_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_fType_1647_);
lean_del_object(v___x_1643_);
v_a_1818_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1669_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1669_);
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
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_fType_1647_);
lean_del_object(v___x_1643_);
v_a_1826_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1667_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1667_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
v___jp_1834_:
{
if (v___x_1652_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc_ref_n(v_args_1648_, 2);
lean_inc_ref(v_fType_1647_);
lean_inc_ref(v_value_1646_);
lean_inc_ref(v_params_1645_);
lean_dec(v_val_1641_);
v___x_1842_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1651_);
v___x_1843_ = l_Array_toSubarray___redArg(v_args_1648_, v___x_1842_, v___x_1651_);
lean_inc_ref(v___x_1843_);
v___x_1844_ = l_Subarray_copy___redArg(v___x_1843_);
v___x_1845_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1645_, v_value_1646_, v___x_1844_, v___x_1652_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v_params_1645_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; lean_object* v___f_1850_; uint8_t v___x_1851_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = 0;
v___x_1848_ = lean_box(v___x_1847_);
lean_inc_ref(v_k_1622_);
lean_inc(v_fvarId_1631_);
lean_inc(v___x_1651_);
v___f_1849_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1849_, 0, v___x_1651_);
lean_closure_set(v___f_1849_, 1, v___x_1650_);
lean_closure_set(v___f_1849_, 2, v_fvarId_1631_);
lean_closure_set(v___f_1849_, 3, v_k_1622_);
lean_closure_set(v___f_1849_, 4, v_args_1648_);
lean_closure_set(v___f_1849_, 5, v___x_1848_);
lean_closure_set(v___f_1849_, 6, v___x_1842_);
lean_inc_ref(v___y_1837_);
lean_inc_ref(v___y_1835_);
lean_inc_ref(v___f_1849_);
lean_inc(v___y_1836_);
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1850_, 0, v___y_1836_);
lean_closure_set(v___f_1850_, 1, v___f_1849_);
lean_closure_set(v___f_1850_, 2, v___y_1835_);
lean_closure_set(v___f_1850_, 3, v___y_1837_);
v___x_1851_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1622_, v_fvarId_1631_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
if (v___x_1851_ == 0)
{
lean_dec(v___x_1651_);
v___y_1654_ = v___y_1835_;
v___y_1655_ = v___x_1843_;
v___y_1656_ = v_a_1846_;
v___y_1657_ = v___y_1836_;
v___y_1658_ = v___f_1849_;
v___y_1659_ = v___f_1850_;
v___y_1660_ = v___y_1838_;
v___y_1661_ = v___y_1837_;
v___y_1662_ = v___y_1841_;
v___y_1663_ = v___x_1847_;
v___y_1664_ = v___y_1840_;
v___y_1665_ = v___x_1842_;
v___y_1666_ = v___y_1839_;
goto v___jp_1653_;
}
else
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_nat_dec_eq(v___x_1650_, v___x_1651_);
lean_dec(v___x_1651_);
if (v___x_1852_ == 0)
{
v___y_1654_ = v___y_1835_;
v___y_1655_ = v___x_1843_;
v___y_1656_ = v_a_1846_;
v___y_1657_ = v___y_1836_;
v___y_1658_ = v___f_1849_;
v___y_1659_ = v___f_1850_;
v___y_1660_ = v___y_1838_;
v___y_1661_ = v___y_1837_;
v___y_1662_ = v___y_1841_;
v___y_1663_ = v___x_1847_;
v___y_1664_ = v___y_1840_;
v___y_1665_ = v___x_1842_;
v___y_1666_ = v___y_1839_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1853_; 
lean_dec_ref(v___f_1850_);
lean_dec_ref(v___f_1849_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v_fType_1647_);
lean_del_object(v___x_1643_);
v___x_1853_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1836_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v___x_1853_);
lean_inc_ref(v___y_1840_);
v___x_1854_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1846_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v___y_1835_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1854_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1854_);
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
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_a_1846_);
lean_dec_ref(v___y_1835_);
v_a_1872_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1853_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1853_);
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
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___x_1843_);
lean_dec_ref(v___y_1835_);
lean_dec(v___x_1651_);
lean_dec_ref(v_args_1648_);
lean_dec_ref(v_fType_1647_);
lean_del_object(v___x_1643_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
v_a_1880_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1845_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1845_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v___x_1888_; 
lean_dec(v___x_1651_);
lean_del_object(v___x_1643_);
v___x_1888_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1641_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_fvarId_1890_; lean_object* v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v_fvarId_1890_ = lean_ctor_get(v_a_1889_, 0);
lean_inc(v_fvarId_1890_);
v___x_1891_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1631_, v_fvarId_1890_, v___y_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref(v___x_1891_);
v___x_1892_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1836_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v___x_1892_);
v___x_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_a_1889_);
lean_ctor_set(v___x_1893_, 1, v_k_1622_);
lean_inc_ref(v___y_1840_);
v___x_1894_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1893_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v___y_1835_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1895_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1894_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1894_);
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
lean_dec(v_a_1889_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_k_1622_);
v_a_1912_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1892_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1892_);
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
lean_dec(v_a_1889_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_k_1622_);
v_a_1920_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1891_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1891_);
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
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v___y_1835_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
v_a_1928_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1888_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1888_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
lean_dec(v_a_1637_);
lean_del_object(v___x_1634_);
lean_dec(v_value_1632_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
v___x_1957_ = lean_box(0);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1957_);
v___x_1959_ = v___x_1639_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
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
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1634_);
lean_dec(v_value_1632_);
lean_dec(v_fvarId_1631_);
lean_dec_ref(v_k_1622_);
v_a_1962_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1636_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1636_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = 0;
v___x_1974_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_typeName_1987_; lean_object* v_discr_1988_; lean_object* v___x_1989_; lean_object* v_subst_1990_; uint8_t v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v_typeName_1987_ = lean_ctor_get(v_cases_1975_, 0);
v_discr_1988_ = lean_ctor_get(v_cases_1975_, 2);
v___x_1989_ = lean_st_ref_get(v_a_1977_);
v_subst_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc_ref(v_subst_1990_);
lean_dec(v___x_1989_);
v___x_1991_ = 0;
v___x_1992_ = 0;
lean_inc(v_discr_1988_);
v___x_1993_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1990_, v_discr_1988_, v___x_1992_);
lean_dec_ref(v_subst_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_fvarId_1994_; lean_object* v___x_1995_; 
v_fvarId_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_fvarId_1994_);
lean_dec_ref(v___x_1993_);
v___x_1995_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_1994_, v_a_1978_, v_a_1980_, v_a_1982_);
lean_dec(v_fvarId_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2225_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2225_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2225_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
if (lean_obj_tag(v_a_1996_) == 1)
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2220_; 
v_val_2000_ = lean_ctor_get(v_a_1996_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_1996_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2002_ = v_a_1996_;
v_isShared_2003_ = v_isSharedCheck_2220_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v_a_1996_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2220_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v_env_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = lean_st_ref_get(v_a_1982_);
v_env_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2004_);
v___x_2006_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_2000_);
lean_inc(v___x_2006_);
v___x_2007_ = l_Lean_Environment_find_x3f(v_env_2005_, v___x_2006_, v___x_1992_);
if (lean_obj_tag(v___x_2007_) == 1)
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2219_; 
v_val_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2219_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2219_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_val_2008_) == 6)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2218_; 
v_val_2012_ = lean_ctor_get(v_val_2008_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_val_2008_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2014_ = v_val_2008_;
v_isShared_2015_ = v_isSharedCheck_2218_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_val_2008_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2218_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_induct_2016_; uint8_t v___x_2017_; 
v_induct_2016_ = lean_ctor_get(v_val_2012_, 1);
lean_inc(v_induct_2016_);
lean_dec_ref(v_val_2012_);
v___x_2017_ = lean_name_eq(v_typeName_1987_, v_induct_2016_);
lean_dec(v_induct_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_del_object(v___x_2014_);
lean_del_object(v___x_2010_);
lean_dec(v___x_2006_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
lean_dec_ref(v_cases_1975_);
v___x_2018_ = lean_box(0);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2018_);
v___x_2020_ = v___x_1998_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v___x_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2217_; 
lean_del_object(v___x_1998_);
v___x_2022_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1991_, v_cases_1975_, v___x_2006_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
v_snd_2024_ = lean_ctor_get(v___x_2022_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2026_ = v___x_2022_;
v_isShared_2027_ = v_isSharedCheck_2217_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snd_2024_);
lean_inc(v_fst_2023_);
lean_dec(v___x_2022_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2217_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 4);
lean_ctor_set(v___x_2014_, 0, v_snd_2024_);
v___x_2029_ = v___x_2014_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_snd_2024_);
v___x_2029_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1991_, v___x_2029_, v_a_1980_);
lean_dec_ref(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2031_; 
lean_dec_ref(v___x_2030_);
v___x_2031_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1977_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref(v___x_2031_);
if (lean_obj_tag(v_fst_2023_) == 0)
{
if (lean_obj_tag(v_val_2000_) == 0)
{
lean_object* v_params_2032_; lean_object* v_code_2033_; lean_object* v_val_2034_; lean_object* v_args_2035_; lean_object* v_lower_2037_; lean_object* v_upper_2038_; lean_object* v_numParams_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
lean_del_object(v___x_2026_);
lean_del_object(v___x_2002_);
v_params_2032_ = lean_ctor_get(v_fst_2023_, 1);
lean_inc_ref(v_params_2032_);
v_code_2033_ = lean_ctor_get(v_fst_2023_, 2);
lean_inc_ref(v_code_2033_);
lean_dec_ref(v_fst_2023_);
v_val_2034_ = lean_ctor_get(v_val_2000_, 0);
lean_inc_ref(v_val_2034_);
v_args_2035_ = lean_ctor_get(v_val_2000_, 1);
lean_inc_ref(v_args_2035_);
lean_dec_ref(v_val_2000_);
v_numParams_2081_ = lean_ctor_get(v_val_2034_, 3);
lean_inc(v_numParams_2081_);
lean_dec_ref(v_val_2034_);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_array_get_size(v_args_2035_);
v___x_2084_ = lean_nat_dec_le(v_numParams_2081_, v___x_2082_);
if (v___x_2084_ == 0)
{
v_lower_2037_ = v_numParams_2081_;
v_upper_2038_ = v___x_2083_;
goto v___jp_2036_;
}
else
{
lean_dec(v_numParams_2081_);
v_lower_2037_ = v___x_2082_;
v_upper_2038_ = v___x_2083_;
goto v___jp_2036_;
}
v___jp_2036_:
{
lean_object* v___x_2039_; size_t v_sz_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2039_ = l_Array_toSubarray___redArg(v_args_2035_, v_lower_2037_, v_upper_2038_);
v_sz_2040_ = lean_array_size(v_params_2032_);
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2032_, v_sz_2040_, v___x_2041_, v___x_2039_, v_a_1977_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; 
lean_dec_ref(v___x_2042_);
lean_inc_ref(v_a_1981_);
v___x_2043_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2033_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1991_, v_params_2032_, v_a_1980_);
lean_dec_ref(v_params_2032_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v___x_2045_, 0);
lean_dec(v_unused_2056_);
v___x_2047_ = v___x_2045_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_dec(v___x_2045_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_a_2044_);
v___x_2050_ = v___x_2010_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2044_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2050_);
v___x_2052_ = v___x_2047_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_2044_);
lean_del_object(v___x_2010_);
v_a_2057_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2045_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2045_);
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
lean_dec_ref(v_params_2032_);
lean_del_object(v___x_2010_);
v_a_2065_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2043_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2043_);
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
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_code_2033_);
lean_dec_ref(v_params_2032_);
lean_del_object(v___x_2010_);
v_a_2073_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2042_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2042_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
else
{
lean_object* v_params_2085_; lean_object* v_code_2086_; lean_object* v_n_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2178_; 
v_params_2085_ = lean_ctor_get(v_fst_2023_, 1);
lean_inc_ref(v_params_2085_);
v_code_2086_ = lean_ctor_get(v_fst_2023_, 2);
lean_inc_ref(v_code_2086_);
lean_dec_ref(v_fst_2023_);
v_n_2087_ = lean_ctor_get(v_val_2000_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_val_2000_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2089_ = v_val_2000_;
v_isShared_2090_ = v_isSharedCheck_2178_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_n_2087_);
lean_dec(v_val_2000_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2178_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_zero_2091_; uint8_t v_isZero_2092_; 
v_zero_2091_ = lean_unsigned_to_nat(0u);
v_isZero_2092_ = lean_nat_dec_eq(v_n_2087_, v_zero_2091_);
if (v_isZero_2092_ == 1)
{
lean_object* v___x_2093_; 
lean_del_object(v___x_2089_);
lean_dec(v_n_2087_);
lean_dec_ref(v_params_2085_);
lean_del_object(v___x_2026_);
lean_del_object(v___x_2002_);
lean_inc_ref(v_a_1981_);
v___x_2093_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2086_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2104_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2104_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2104_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_a_2094_);
v___x_2099_ = v___x_2010_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2099_);
v___x_2101_ = v___x_2096_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
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
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_del_object(v___x_2010_);
v_a_2105_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2093_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2093_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_one_2113_; lean_object* v_n_2114_; lean_object* v___x_2116_; 
v_one_2113_ = lean_unsigned_to_nat(1u);
v_n_2114_ = lean_nat_sub(v_n_2087_, v_one_2113_);
lean_dec(v_n_2087_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 0);
lean_ctor_set(v___x_2089_, 0, v_n_2114_);
v___x_2116_ = v___x_2089_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_n_2114_);
v___x_2116_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2116_);
v___x_2118_ = v___x_2002_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2120_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1991_, v___x_2118_, v___x_2119_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_fvarId_2124_; lean_object* v_fvarId_2125_; lean_object* v___x_2126_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2123_ = lean_array_get_borrowed(v___x_2122_, v_params_2085_, v_zero_2091_);
v_fvarId_2124_ = lean_ctor_get(v___x_2123_, 0);
v_fvarId_2125_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fvarId_2125_);
lean_inc(v_fvarId_2124_);
v___x_2126_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2124_, v_fvarId_2125_, v_a_1977_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref(v___x_2126_);
lean_inc_ref(v_a_1981_);
v___x_2127_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2086_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1991_, v_params_2085_, v_a_1980_);
lean_dec_ref(v_params_2085_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2142_; 
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2129_, 0);
lean_dec(v_unused_2143_);
v___x_2131_ = v___x_2129_;
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v___x_2129_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v_a_2128_);
lean_ctor_set(v___x_2026_, 0, v_a_2121_);
v___x_2134_ = v___x_2026_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2121_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2128_);
v___x_2134_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2134_);
v___x_2136_ = v___x_2010_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2136_);
v___x_2138_ = v___x_2131_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2128_);
lean_dec(v_a_2121_);
lean_del_object(v___x_2026_);
lean_del_object(v___x_2010_);
v_a_2144_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2129_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2129_);
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
lean_dec(v_a_2121_);
lean_dec_ref(v_params_2085_);
lean_del_object(v___x_2026_);
lean_del_object(v___x_2010_);
v_a_2152_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2127_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2127_);
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
lean_dec(v_a_2121_);
lean_dec_ref(v_code_2086_);
lean_dec_ref(v_params_2085_);
lean_del_object(v___x_2026_);
lean_del_object(v___x_2010_);
v_a_2160_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2126_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2126_);
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
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v_code_2086_);
lean_dec_ref(v_params_2085_);
lean_del_object(v___x_2026_);
lean_del_object(v___x_2010_);
v_a_2168_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2120_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2120_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
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
lean_object* v_code_2179_; lean_object* v___x_2180_; 
lean_del_object(v___x_2026_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
v_code_2179_ = lean_ctor_get(v_fst_2023_, 0);
lean_inc_ref(v_code_2179_);
lean_dec_ref(v_fst_2023_);
lean_inc_ref(v_a_1981_);
v___x_2180_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2179_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2191_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2191_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2191_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_a_2181_);
v___x_2186_ = v___x_2010_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2186_);
v___x_2188_ = v___x_2183_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
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
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2010_);
v_a_2192_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2180_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2180_);
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
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_2026_);
lean_dec(v_fst_2023_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
v_a_2200_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2031_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2031_);
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
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_del_object(v___x_2026_);
lean_dec(v_fst_2023_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
v_a_2208_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2030_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2030_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
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
}
}
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
lean_dec(v___x_2006_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
lean_del_object(v___x_1998_);
lean_dec_ref(v_cases_1975_);
goto v___jp_1984_;
}
}
}
else
{
lean_dec(v___x_2007_);
lean_dec(v___x_2006_);
lean_del_object(v___x_2002_);
lean_dec(v_val_2000_);
lean_del_object(v___x_1998_);
lean_dec_ref(v_cases_1975_);
goto v___jp_1984_;
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_dec(v_a_1996_);
lean_dec_ref(v_cases_1975_);
v___x_2221_ = lean_box(0);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2221_);
v___x_2223_ = v___x_1998_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
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
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_cases_1975_);
v_a_2226_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_1995_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_1995_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2234_; 
lean_dec_ref(v_cases_1975_);
v___x_2234_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1991_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2243_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
v_a_2244_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2234_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2234_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2252_, lean_object* v_i_2253_, lean_object* v_as_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = lean_array_get_size(v_as_2254_);
v___x_2264_ = lean_nat_dec_lt(v_i_2253_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_as_2254_);
return v___x_2265_;
}
else
{
lean_object* v_a_2266_; lean_object* v_a_2268_; 
v_a_2266_ = lean_array_fget_borrowed(v_as_2254_, v_i_2253_);
if (lean_obj_tag(v_a_2266_) == 0)
{
lean_object* v_ctorName_2279_; lean_object* v_params_2280_; lean_object* v_code_2281_; uint8_t v___x_2304_; uint8_t v_a_2306_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_ctorName_2279_ = lean_ctor_get(v_a_2266_, 0);
v_params_2280_ = lean_ctor_get(v_a_2266_, 1);
v_code_2281_ = lean_ctor_get(v_a_2266_, 2);
v___x_2304_ = 0;
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_array_get_size(v_params_2280_);
v___x_2339_ = lean_nat_dec_lt(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
v_a_2306_ = v___x_2339_;
goto v___jp_2305_;
}
else
{
if (v___x_2339_ == 0)
{
v_a_2306_ = v___x_2339_;
goto v___jp_2305_;
}
else
{
size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = lean_usize_of_nat(v___x_2338_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2280_, v___x_2340_, v___x_2341_, v___y_2261_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
v_a_2306_ = v___x_2344_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2345_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2342_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2342_);
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
}
v___jp_2282_:
{
lean_object* v___x_2283_; 
lean_inc_ref(v_params_2280_);
lean_inc(v_ctorName_2279_);
lean_inc(v_fvarId_2252_);
v___x_2283_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2252_, v_ctorName_2279_, v_params_2280_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2283_);
lean_inc_ref(v___y_2260_);
lean_inc_ref(v_code_2281_);
v___x_2285_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2281_, v___y_2255_, v___y_2256_, v_a_2284_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v_a_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
lean_inc_ref(v_a_2266_);
v___x_2287_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2266_, v_a_2286_);
v_a_2268_ = v___x_2287_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2288_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2285_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2285_);
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
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2296_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2283_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2283_);
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
v___jp_2305_:
{
if (lean_obj_tag(v_code_2281_) == 6)
{
goto v___jp_2282_;
}
else
{
if (v_a_2306_ == 0)
{
goto v___jp_2282_;
}
else
{
lean_object* v___x_2307_; 
lean_inc_ref(v_code_2281_);
v___x_2307_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2304_, v_code_2281_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2304_, v_code_2281_, v___y_2259_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2310_; 
lean_dec_ref(v___x_2309_);
v___x_2310_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2256_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v___x_2310_);
v___x_2311_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2311_, 0, v_a_2308_);
lean_inc_ref(v_a_2266_);
v___x_2312_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2266_, v___x_2311_);
v_a_2268_ = v___x_2312_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2308_);
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2313_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2310_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2310_);
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
lean_dec(v_a_2308_);
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2321_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2309_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2309_);
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
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2329_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2307_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2307_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
}
}
else
{
lean_object* v_code_2353_; lean_object* v___x_2354_; 
v_code_2353_ = lean_ctor_get(v_a_2266_, 0);
lean_inc_ref(v___y_2260_);
lean_inc_ref(v_code_2353_);
v___x_2354_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2353_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
lean_inc_ref(v_a_2266_);
v___x_2356_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2266_, v_a_2355_);
v_a_2268_ = v___x_2356_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_as_2254_);
lean_dec(v_i_2253_);
lean_dec(v_fvarId_2252_);
v_a_2357_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2354_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2354_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
v___jp_2267_:
{
size_t v___x_2269_; size_t v___x_2270_; uint8_t v___x_2271_; 
v___x_2269_ = lean_ptr_addr(v_a_2266_);
v___x_2270_ = lean_ptr_addr(v_a_2268_);
v___x_2271_ = lean_usize_dec_eq(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_add(v_i_2253_, v___x_2272_);
v___x_2274_ = lean_array_fset(v_as_2254_, v_i_2253_, v_a_2268_);
lean_dec(v_i_2253_);
v_i_2253_ = v___x_2273_;
v_as_2254_ = v___x_2274_;
goto _start;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v_a_2268_);
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_nat_add(v_i_2253_, v___x_2276_);
lean_dec(v_i_2253_);
v_i_2253_ = v___x_2277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2377_; lean_object* v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2384_; lean_object* v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2411_; lean_object* v___y_2412_; lean_object* v_decl_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v_decl_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v_decl_2483_; lean_object* v_k_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2559_; lean_object* v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v___y_2754_; lean_object* v_decl_2755_; lean_object* v_fvarId_2756_; lean_object* v_type_2757_; lean_object* v_value_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2799_; lean_object* v___y_2800_; uint8_t v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2847_; lean_object* v___y_2848_; uint8_t v___y_2849_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2980_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v_fileName_3023_; lean_object* v_fileMap_3024_; lean_object* v_options_3025_; lean_object* v_currRecDepth_3026_; lean_object* v_maxRecDepth_3027_; lean_object* v_ref_3028_; lean_object* v_currNamespace_3029_; lean_object* v_openDecls_3030_; lean_object* v_initHeartbeats_3031_; lean_object* v_maxHeartbeats_3032_; lean_object* v_quotContext_3033_; lean_object* v_currMacroScope_3034_; uint8_t v_diag_3035_; lean_object* v_cancelTk_x3f_3036_; uint8_t v_suppressElabErrors_3037_; lean_object* v_inheritedTraceOptions_3038_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v_fileName_3023_ = lean_ctor_get(v_a_2371_, 0);
v_fileMap_3024_ = lean_ctor_get(v_a_2371_, 1);
v_options_3025_ = lean_ctor_get(v_a_2371_, 2);
v_currRecDepth_3026_ = lean_ctor_get(v_a_2371_, 3);
v_maxRecDepth_3027_ = lean_ctor_get(v_a_2371_, 4);
v_ref_3028_ = lean_ctor_get(v_a_2371_, 5);
v_currNamespace_3029_ = lean_ctor_get(v_a_2371_, 6);
v_openDecls_3030_ = lean_ctor_get(v_a_2371_, 7);
v_initHeartbeats_3031_ = lean_ctor_get(v_a_2371_, 8);
v_maxHeartbeats_3032_ = lean_ctor_get(v_a_2371_, 9);
v_quotContext_3033_ = lean_ctor_get(v_a_2371_, 10);
v_currMacroScope_3034_ = lean_ctor_get(v_a_2371_, 11);
v_diag_3035_ = lean_ctor_get_uint8(v_a_2371_, sizeof(void*)*14);
v_cancelTk_x3f_3036_ = lean_ctor_get(v_a_2371_, 12);
v_suppressElabErrors_3037_ = lean_ctor_get_uint8(v_a_2371_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3038_ = lean_ctor_get(v_a_2371_, 13);
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_nat_dec_eq(v_maxRecDepth_3027_, v___x_3276_);
if (v___x_3277_ == 0)
{
uint8_t v___x_3278_; 
v___x_3278_ = lean_nat_dec_eq(v_currRecDepth_3026_, v_maxRecDepth_3027_);
if (v___x_3278_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3038_);
lean_inc(v_cancelTk_x3f_3036_);
lean_inc(v_currMacroScope_3034_);
lean_inc(v_quotContext_3033_);
lean_inc(v_maxHeartbeats_3032_);
lean_inc(v_initHeartbeats_3031_);
lean_inc(v_openDecls_3030_);
lean_inc(v_currNamespace_3029_);
lean_inc(v_ref_3028_);
lean_inc(v_maxRecDepth_3027_);
lean_inc(v_currRecDepth_3026_);
lean_inc_ref(v_options_3025_);
lean_inc_ref(v_fileMap_3024_);
lean_inc_ref(v_fileName_3023_);
lean_dec_ref(v_a_2371_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3279_; 
lean_dec_ref(v_code_2365_);
v___x_3279_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec_ref(v_a_2371_);
return v___x_3279_;
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3038_);
lean_inc(v_cancelTk_x3f_3036_);
lean_inc(v_currMacroScope_3034_);
lean_inc(v_quotContext_3033_);
lean_inc(v_maxHeartbeats_3032_);
lean_inc(v_initHeartbeats_3031_);
lean_inc(v_openDecls_3030_);
lean_inc(v_currNamespace_3029_);
lean_inc(v_ref_3028_);
lean_inc(v_maxRecDepth_3027_);
lean_inc(v_currRecDepth_3026_);
lean_inc_ref(v_options_3025_);
lean_inc_ref(v_fileMap_3024_);
lean_inc_ref(v_fileName_3023_);
lean_dec_ref(v_a_2371_);
goto v___jp_3039_;
}
v___jp_2374_:
{
if (v___y_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_code_2365_);
v___x_2378_ = lean_alloc_ctor(1, 2, 0);
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
lean_ctor_set(v___x_2380_, 0, v_code_2365_);
return v___x_2380_;
}
}
v___jp_2381_:
{
if (v___y_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_code_2365_);
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___y_2382_);
lean_ctor_set(v___x_2385_, 1, v___y_2383_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; 
lean_dec_ref(v___y_2383_);
lean_dec_ref(v___y_2382_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_code_2365_);
return v___x_2387_;
}
}
v___jp_2388_:
{
switch(lean_obj_tag(v_code_2365_))
{
case 1:
{
lean_object* v_decl_2391_; lean_object* v_k_2392_; size_t v___x_2393_; size_t v___x_2394_; uint8_t v___x_2395_; 
v_decl_2391_ = lean_ctor_get(v_code_2365_, 0);
v_k_2392_ = lean_ctor_get(v_code_2365_, 1);
v___x_2393_ = lean_ptr_addr(v_k_2392_);
v___x_2394_ = lean_ptr_addr(v___y_2390_);
v___x_2395_ = lean_usize_dec_eq(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
v___y_2375_ = v___y_2389_;
v___y_2376_ = v___y_2390_;
v___y_2377_ = v___x_2395_;
goto v___jp_2374_;
}
else
{
size_t v___x_2396_; size_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_ptr_addr(v_decl_2391_);
v___x_2397_ = lean_ptr_addr(v___y_2389_);
v___x_2398_ = lean_usize_dec_eq(v___x_2396_, v___x_2397_);
v___y_2375_ = v___y_2389_;
v___y_2376_ = v___y_2390_;
v___y_2377_ = v___x_2398_;
goto v___jp_2374_;
}
}
case 2:
{
lean_object* v_decl_2399_; lean_object* v_k_2400_; size_t v___x_2401_; size_t v___x_2402_; uint8_t v___x_2403_; 
v_decl_2399_ = lean_ctor_get(v_code_2365_, 0);
v_k_2400_ = lean_ctor_get(v_code_2365_, 1);
v___x_2401_ = lean_ptr_addr(v_k_2400_);
v___x_2402_ = lean_ptr_addr(v___y_2390_);
v___x_2403_ = lean_usize_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
v___y_2382_ = v___y_2389_;
v___y_2383_ = v___y_2390_;
v___y_2384_ = v___x_2403_;
goto v___jp_2381_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_ptr_addr(v_decl_2399_);
v___x_2405_ = lean_ptr_addr(v___y_2389_);
v___x_2406_ = lean_usize_dec_eq(v___x_2404_, v___x_2405_);
v___y_2382_ = v___y_2389_;
v___y_2383_ = v___y_2390_;
v___y_2384_ = v___x_2406_;
goto v___jp_2381_;
}
}
default: 
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v_code_2365_);
v___x_2407_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2408_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
}
v___jp_2410_:
{
lean_object* v___x_2421_; 
lean_inc_ref(v___y_2419_);
v___x_2421_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2412_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_fvarId_2423_; lean_object* v___x_2424_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
v_fvarId_2423_ = lean_ctor_get(v_decl_2413_, 0);
v___x_2424_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2423_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; uint8_t v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref(v___x_2424_);
v___x_2426_ = lean_unbox(v_a_2425_);
lean_dec(v_a_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_code_2365_);
v___x_2427_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2413_, v___y_2415_, v___y_2418_);
lean_dec_ref(v_decl_2413_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v___x_2427_, 0);
lean_dec(v_unused_2435_);
v___x_2429_ = v___x_2427_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v___x_2427_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v_a_2422_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2422_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2422_);
v_a_2436_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
if (v___y_2411_ == 0)
{
lean_dec_ref(v___y_2419_);
v___y_2389_ = v_decl_2413_;
v___y_2390_ = v_a_2422_;
goto v___jp_2388_;
}
else
{
lean_object* v___x_2444_; 
lean_inc_ref(v_decl_2413_);
v___x_2444_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec_ref(v___y_2419_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref(v___x_2444_);
v___y_2389_ = v_decl_2413_;
v___y_2390_ = v_a_2422_;
goto v___jp_2388_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_a_2422_);
lean_dec_ref(v_decl_2413_);
lean_dec_ref(v_code_2365_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
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
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2422_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_decl_2413_);
lean_dec_ref(v_code_2365_);
v_a_2453_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2424_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2424_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_decl_2413_);
lean_dec_ref(v_code_2365_);
return v___x_2421_;
}
}
v___jp_2461_:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2472_);
v___y_2411_ = v___y_2463_;
v___y_2412_ = v___y_2462_;
v_decl_2413_ = v_a_2473_;
v___y_2414_ = v___y_2465_;
v___y_2415_ = v___y_2466_;
v___y_2416_ = v___y_2467_;
v___y_2417_ = v___y_2468_;
v___y_2418_ = v___y_2469_;
v___y_2419_ = v___y_2470_;
v___y_2420_ = v___y_2471_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v___y_2470_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_code_2365_);
v_a_2474_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2472_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
v___jp_2482_:
{
lean_object* v_fvarId_2492_; lean_object* v_params_2493_; lean_object* v_type_2494_; lean_object* v___x_2495_; 
v_fvarId_2492_ = lean_ctor_get(v_decl_2483_, 0);
v_params_2493_ = lean_ctor_get(v_decl_2483_, 2);
v_type_2494_ = lean_ctor_get(v_decl_2483_, 3);
v___x_2495_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2492_, v___y_2486_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; uint8_t v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = 0;
v___x_2498_ = lean_unbox(v_a_2496_);
if (v___x_2498_ == 0)
{
uint8_t v___x_2499_; 
v___x_2499_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2365_);
if (v___x_2499_ == 0)
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
v___y_2462_ = v_k_2484_;
v___y_2463_ = v___x_2500_;
v_decl_2464_ = v_decl_2483_;
v___y_2465_ = v___y_2485_;
v___y_2466_ = v___y_2486_;
v___y_2467_ = v___y_2487_;
v___y_2468_ = v___y_2488_;
v___y_2469_ = v___y_2489_;
v___y_2470_ = v___y_2490_;
v___y_2471_ = v___y_2491_;
goto v___jp_2461_;
}
else
{
uint8_t v___x_2501_; 
lean_inc_ref(v_type_2494_);
v___x_2501_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2494_, v_params_2493_);
if (v___x_2501_ == 0)
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
v___y_2462_ = v_k_2484_;
v___y_2463_ = v___x_2502_;
v_decl_2464_ = v_decl_2483_;
v___y_2465_ = v___y_2485_;
v___y_2466_ = v___y_2486_;
v___y_2467_ = v___y_2487_;
v___y_2468_ = v___y_2488_;
v___y_2469_ = v___y_2489_;
v___y_2470_ = v___y_2490_;
v___y_2471_ = v___y_2491_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2503_; lean_object* v_subst_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = lean_st_ref_get(v___y_2486_);
v_subst_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_ref(v_subst_2504_);
lean_dec(v___x_2503_);
v___x_2505_ = lean_unbox(v_a_2496_);
v___x_2506_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2497_, v___x_2505_, v_decl_2483_, v_subst_2504_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec_ref(v_subst_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2507_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2486_);
if (lean_obj_tag(v___x_2510_) == 0)
{
uint8_t v___x_2511_; 
lean_dec_ref(v___x_2510_);
v___x_2511_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
v___y_2462_ = v_k_2484_;
v___y_2463_ = v___x_2511_;
v_decl_2464_ = v_a_2509_;
v___y_2465_ = v___y_2485_;
v___y_2466_ = v___y_2486_;
v___y_2467_ = v___y_2487_;
v___y_2468_ = v___y_2488_;
v___y_2469_ = v___y_2489_;
v___y_2470_ = v___y_2490_;
v___y_2471_ = v___y_2491_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_a_2509_);
lean_dec(v_a_2496_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_k_2484_);
lean_dec_ref(v_code_2365_);
v_a_2512_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2510_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2510_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2496_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_k_2484_);
lean_dec_ref(v_code_2365_);
v_a_2520_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2508_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2508_);
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
lean_dec(v_a_2496_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_k_2484_);
lean_dec_ref(v_code_2365_);
v_a_2528_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2506_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2506_);
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
}
}
else
{
lean_object* v___x_2536_; lean_object* v_subst_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_st_ref_get(v___y_2486_);
v_subst_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_subst_2537_);
lean_dec(v___x_2536_);
v___x_2538_ = 0;
v___x_2539_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2497_, v___x_2538_, v_decl_2483_, v_subst_2537_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec_ref(v_subst_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; uint8_t v___x_2541_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
v___y_2411_ = v___x_2541_;
v___y_2412_ = v_k_2484_;
v_decl_2413_ = v_a_2540_;
v___y_2414_ = v___y_2485_;
v___y_2415_ = v___y_2486_;
v___y_2416_ = v___y_2487_;
v___y_2417_ = v___y_2488_;
v___y_2418_ = v___y_2489_;
v___y_2419_ = v___y_2490_;
v___y_2420_ = v___y_2491_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2496_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_k_2484_);
lean_dec_ref(v_code_2365_);
v_a_2542_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2539_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2539_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_k_2484_);
lean_dec_ref(v_decl_2483_);
lean_dec_ref(v_code_2365_);
v_a_2550_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2495_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2495_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
v___jp_2558_:
{
if (v___y_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec_ref(v_code_2365_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___y_2559_);
lean_ctor_set(v___x_2562_, 1, v___y_2560_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; 
lean_dec_ref(v___y_2560_);
lean_dec_ref(v___y_2559_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_code_2365_);
return v___x_2564_;
}
}
v___jp_2565_:
{
lean_object* v___x_2576_; 
lean_inc_ref(v___y_2569_);
v___x_2576_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2569_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref(v___x_2576_);
if (lean_obj_tag(v_a_2577_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2579_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_val_2578_ = lean_ctor_get(v_a_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref(v_a_2577_);
v___x_2579_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2568_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; 
lean_dec_ref(v___x_2579_);
lean_inc_ref(v___y_2572_);
v___x_2580_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2575_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2578_, v_a_2581_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
lean_dec_ref(v___y_2572_);
lean_dec(v_val_2578_);
return v___x_2582_;
}
else
{
lean_dec(v_val_2578_);
lean_dec_ref(v___y_2572_);
return v___x_2580_;
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_val_2578_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
v_a_2583_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2579_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v___x_2591_; 
lean_dec(v_a_2577_);
lean_inc_ref(v___y_2569_);
v___x_2591_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2569_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_val_2593_; lean_object* v___x_2594_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_val_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2593_);
lean_dec_ref(v_a_2592_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_val_2593_);
lean_ctor_set(v___x_2594_, 1, v___y_2575_);
v_code_2365_ = v___x_2594_;
v_a_2366_ = v___y_2567_;
v_a_2367_ = v___y_2568_;
v_a_2368_ = v___y_2574_;
v_a_2369_ = v___y_2566_;
v_a_2370_ = v___y_2573_;
v_a_2371_ = v___y_2572_;
v_a_2372_ = v___y_2570_;
goto _start;
}
else
{
lean_object* v_fvarId_2596_; lean_object* v_value_2597_; lean_object* v___x_2598_; 
lean_dec(v_a_2592_);
v_fvarId_2596_ = lean_ctor_get(v___y_2569_, 0);
v_value_2597_ = lean_ctor_get(v___y_2569_, 3);
v___x_2598_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2597_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
if (lean_obj_tag(v_a_2599_) == 1)
{
lean_object* v_val_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_code_2365_);
v_val_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v_a_2599_);
lean_inc(v_fvarId_2596_);
v___x_2601_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2596_, v_val_2600_, v___y_2568_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref(v___x_2601_);
v___x_2602_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2569_, v___y_2568_, v___y_2573_);
lean_dec_ref(v___y_2569_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_dec_ref(v___x_2602_);
v_code_2365_ = v___y_2575_;
v_a_2366_ = v___y_2567_;
v_a_2367_ = v___y_2568_;
v_a_2368_ = v___y_2574_;
v_a_2369_ = v___y_2566_;
v_a_2370_ = v___y_2573_;
v_a_2371_ = v___y_2572_;
v_a_2372_ = v___y_2570_;
goto _start;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
v_a_2604_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2602_);
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
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2569_);
v_a_2612_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2601_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2601_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v___x_2620_; 
lean_dec(v_a_2599_);
lean_inc_ref(v___y_2575_);
lean_inc_ref(v___y_2569_);
v___x_2620_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2569_, v___y_2575_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref(v___x_2620_);
if (lean_obj_tag(v_a_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_code_2365_);
v_val_2622_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref(v_a_2621_);
v___x_2623_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2569_, v___y_2568_, v___y_2573_);
lean_dec_ref(v___y_2569_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2623_, 0);
lean_dec(v_unused_2631_);
v___x_2625_ = v___x_2623_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_dec(v___x_2623_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_val_2622_);
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_val_2622_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_val_2622_);
v_a_2632_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2623_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2623_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v___x_2640_; 
lean_dec(v_a_2621_);
lean_inc(v_value_2597_);
v___x_2640_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2597_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
if (lean_obj_tag(v_a_2641_) == 1)
{
lean_object* v_val_2642_; lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___x_2645_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_code_2365_);
v_val_2642_ = lean_ctor_get(v_a_2641_, 0);
lean_inc(v_val_2642_);
lean_dec_ref(v_a_2641_);
v_fst_2643_ = lean_ctor_get(v_val_2642_, 0);
lean_inc(v_fst_2643_);
v_snd_2644_ = lean_ctor_get(v_val_2642_, 1);
lean_inc(v_snd_2644_);
lean_dec(v_val_2642_);
lean_inc(v_fvarId_2596_);
v___x_2645_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2596_, v_snd_2644_, v___y_2568_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2645_);
v___x_2646_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2569_, v___y_2568_, v___y_2573_);
lean_dec_ref(v___y_2569_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2647_; 
lean_dec_ref(v___x_2646_);
lean_inc_ref(v___y_2572_);
v___x_2647_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2575_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2643_, v_a_2648_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
lean_dec_ref(v___y_2572_);
lean_dec(v_fst_2643_);
return v___x_2649_;
}
else
{
lean_dec(v_fst_2643_);
lean_dec_ref(v___y_2572_);
return v___x_2647_;
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_fst_2643_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
v_a_2650_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2646_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2646_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_fst_2643_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2569_);
v_a_2658_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2645_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v___x_2666_; 
lean_dec(v_a_2641_);
lean_inc_ref(v___y_2572_);
lean_inc_ref(v___y_2575_);
v___x_2666_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2575_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2596_, v___y_2568_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; uint8_t v___x_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = lean_unbox(v_a_2669_);
lean_dec(v_a_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_code_2365_);
v___x_2671_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2569_, v___y_2568_, v___y_2573_);
lean_dec_ref(v___y_2569_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2671_, 0);
lean_dec(v_unused_2679_);
v___x_2673_ = v___x_2671_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v___x_2671_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v_a_2667_);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2667_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_a_2667_);
v_a_2680_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2671_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2671_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v___x_2688_; 
lean_inc_ref(v___y_2569_);
v___x_2688_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2569_, v___y_2567_, v___y_2568_, v___y_2574_, v___y_2566_, v___y_2573_, v___y_2572_, v___y_2570_);
lean_dec_ref(v___y_2572_);
if (lean_obj_tag(v___x_2688_) == 0)
{
size_t v___x_2689_; size_t v___x_2690_; uint8_t v___x_2691_; 
lean_dec_ref(v___x_2688_);
v___x_2689_ = lean_ptr_addr(v___y_2575_);
lean_dec_ref(v___y_2575_);
v___x_2690_ = lean_ptr_addr(v_a_2667_);
v___x_2691_ = lean_usize_dec_eq(v___x_2689_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec_ref(v___y_2571_);
v___y_2559_ = v___y_2569_;
v___y_2560_ = v_a_2667_;
v___y_2561_ = v___x_2691_;
goto v___jp_2558_;
}
else
{
size_t v___x_2692_; size_t v___x_2693_; uint8_t v___x_2694_; 
v___x_2692_ = lean_ptr_addr(v___y_2571_);
lean_dec_ref(v___y_2571_);
v___x_2693_ = lean_ptr_addr(v___y_2569_);
v___x_2694_ = lean_usize_dec_eq(v___x_2692_, v___x_2693_);
v___y_2559_ = v___y_2569_;
v___y_2560_ = v_a_2667_;
v___y_2561_ = v___x_2694_;
goto v___jp_2558_;
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2667_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2695_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2688_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2688_);
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
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2667_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2703_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2668_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2668_);
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
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
return v___x_2666_;
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2711_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2640_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2640_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2719_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2620_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2620_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
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
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2727_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2598_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2598_);
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
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2735_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2591_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2591_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_code_2365_);
v_a_2743_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2576_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2576_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
v___jp_2751_:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Expr_isErased(v_type_2757_);
lean_dec_ref(v_type_2757_);
if (v___x_2766_ == 0)
{
lean_dec(v_value_2758_);
lean_dec(v_fvarId_2756_);
v___y_2566_ = v___y_2762_;
v___y_2567_ = v___y_2759_;
v___y_2568_ = v___y_2760_;
v___y_2569_ = v_decl_2755_;
v___y_2570_ = v___y_2765_;
v___y_2571_ = v___y_2752_;
v___y_2572_ = v___y_2764_;
v___y_2573_ = v___y_2763_;
v___y_2574_ = v___y_2761_;
v___y_2575_ = v___y_2754_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_box(1);
v___x_2768_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___y_2753_, v_value_2758_, v___x_2767_);
lean_dec(v_value_2758_);
if (v___x_2768_ == 0)
{
if (v___x_2766_ == 0)
{
lean_dec(v_fvarId_2756_);
v___y_2566_ = v___y_2762_;
v___y_2567_ = v___y_2759_;
v___y_2568_ = v___y_2760_;
v___y_2569_ = v_decl_2755_;
v___y_2570_ = v___y_2765_;
v___y_2571_ = v___y_2752_;
v___y_2572_ = v___y_2764_;
v___y_2573_ = v___y_2763_;
v___y_2574_ = v___y_2761_;
v___y_2575_ = v___y_2754_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2769_; lean_object* v_subst_2770_; lean_object* v_used_2771_; lean_object* v_binderRenaming_2772_; lean_object* v_funDeclInfoMap_2773_; uint8_t v_simplified_2774_; lean_object* v_visited_2775_; lean_object* v_inline_2776_; lean_object* v_inlineLocal_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v___y_2752_);
lean_dec_ref(v_code_2365_);
v___x_2769_ = lean_st_ref_take(v___y_2760_);
v_subst_2770_ = lean_ctor_get(v___x_2769_, 0);
v_used_2771_ = lean_ctor_get(v___x_2769_, 1);
v_binderRenaming_2772_ = lean_ctor_get(v___x_2769_, 2);
v_funDeclInfoMap_2773_ = lean_ctor_get(v___x_2769_, 3);
v_simplified_2774_ = lean_ctor_get_uint8(v___x_2769_, sizeof(void*)*7);
v_visited_2775_ = lean_ctor_get(v___x_2769_, 4);
v_inline_2776_ = lean_ctor_get(v___x_2769_, 5);
v_inlineLocal_2777_ = lean_ctor_get(v___x_2769_, 6);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2779_ = v___x_2769_;
v_isShared_2780_ = v_isSharedCheck_2797_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_inlineLocal_2777_);
lean_inc(v_inline_2776_);
lean_inc(v_visited_2775_);
lean_inc(v_funDeclInfoMap_2773_);
lean_inc(v_binderRenaming_2772_);
lean_inc(v_used_2771_);
lean_inc(v_subst_2770_);
lean_dec(v___x_2769_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2797_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2770_, v_fvarId_2756_, v___x_2781_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2782_);
v___x_2784_ = v___x_2779_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_used_2771_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_binderRenaming_2772_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_funDeclInfoMap_2773_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_visited_2775_);
lean_ctor_set(v_reuseFailAlloc_2796_, 5, v_inline_2776_);
lean_ctor_set(v_reuseFailAlloc_2796_, 6, v_inlineLocal_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2796_, sizeof(void*)*7, v_simplified_2774_);
v___x_2784_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_st_ref_set(v___y_2760_, v___x_2784_);
v___x_2786_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2755_, v___y_2760_, v___y_2763_);
lean_dec_ref(v_decl_2755_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_dec_ref(v___x_2786_);
v_code_2365_ = v___y_2754_;
v_a_2366_ = v___y_2759_;
v_a_2367_ = v___y_2760_;
v_a_2368_ = v___y_2761_;
v_a_2369_ = v___y_2762_;
v_a_2370_ = v___y_2763_;
v_a_2371_ = v___y_2764_;
v_a_2372_ = v___y_2765_;
goto _start;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v___y_2764_);
lean_dec_ref(v___y_2754_);
v_a_2788_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2786_);
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
}
}
}
else
{
lean_dec(v_fvarId_2756_);
v___y_2566_ = v___y_2762_;
v___y_2567_ = v___y_2759_;
v___y_2568_ = v___y_2760_;
v___y_2569_ = v_decl_2755_;
v___y_2570_ = v___y_2765_;
v___y_2571_ = v___y_2752_;
v___y_2572_ = v___y_2764_;
v___y_2573_ = v___y_2763_;
v___y_2574_ = v___y_2761_;
v___y_2575_ = v___y_2754_;
goto v___jp_2565_;
}
}
}
v___jp_2798_:
{
lean_object* v_fvarId_2810_; lean_object* v_type_2811_; lean_object* v_value_2812_; lean_object* v___x_2813_; 
v_fvarId_2810_ = lean_ctor_get(v___y_2800_, 0);
v_type_2811_ = lean_ctor_get(v___y_2800_, 2);
v_value_2812_ = lean_ctor_get(v___y_2800_, 3);
lean_inc(v_value_2812_);
v___x_2813_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2812_, v___y_2803_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
if (lean_obj_tag(v_a_2814_) == 1)
{
lean_object* v_val_2815_; lean_object* v___x_2816_; 
v_val_2815_ = lean_ctor_get(v_a_2814_, 0);
lean_inc(v_val_2815_);
lean_dec_ref(v_a_2814_);
v___x_2816_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2804_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; 
lean_dec_ref(v___x_2816_);
v___x_2817_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___y_2801_, v___y_2800_, v_val_2815_, v___y_2807_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v_fvarId_2819_; lean_object* v_type_2820_; lean_object* v_value_2821_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v_fvarId_2819_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_fvarId_2819_);
v_type_2820_ = lean_ctor_get(v_a_2818_, 2);
lean_inc_ref(v_type_2820_);
v_value_2821_ = lean_ctor_get(v_a_2818_, 3);
lean_inc(v_value_2821_);
v___y_2752_ = v___y_2799_;
v___y_2753_ = v___y_2801_;
v___y_2754_ = v___y_2802_;
v_decl_2755_ = v_a_2818_;
v_fvarId_2756_ = v_fvarId_2819_;
v_type_2757_ = v_type_2820_;
v_value_2758_ = v_value_2821_;
v___y_2759_ = v___y_2803_;
v___y_2760_ = v___y_2804_;
v___y_2761_ = v___y_2805_;
v___y_2762_ = v___y_2806_;
v___y_2763_ = v___y_2807_;
v___y_2764_ = v___y_2808_;
v___y_2765_ = v___y_2809_;
goto v___jp_2751_;
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v___y_2808_);
lean_dec_ref(v___y_2802_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_code_2365_);
v_a_2822_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2817_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2817_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_val_2815_);
lean_dec_ref(v___y_2808_);
lean_dec_ref(v___y_2802_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_code_2365_);
v_a_2830_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2816_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2816_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_inc(v_value_2812_);
lean_inc_ref(v_type_2811_);
lean_inc(v_fvarId_2810_);
lean_dec(v_a_2814_);
v___y_2752_ = v___y_2799_;
v___y_2753_ = v___y_2801_;
v___y_2754_ = v___y_2802_;
v_decl_2755_ = v___y_2800_;
v_fvarId_2756_ = v_fvarId_2810_;
v_type_2757_ = v_type_2811_;
v_value_2758_ = v_value_2812_;
v___y_2759_ = v___y_2803_;
v___y_2760_ = v___y_2804_;
v___y_2761_ = v___y_2805_;
v___y_2762_ = v___y_2806_;
v___y_2763_ = v___y_2807_;
v___y_2764_ = v___y_2808_;
v___y_2765_ = v___y_2809_;
goto v___jp_2751_;
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec_ref(v___y_2808_);
lean_dec_ref(v___y_2802_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_code_2365_);
v_a_2838_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2813_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2813_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
v___jp_2846_:
{
if (v___y_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec_ref(v_code_2365_);
v___x_2850_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___y_2848_);
lean_ctor_set(v___x_2850_, 1, v___y_2847_);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
else
{
lean_object* v___x_2852_; 
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_code_2365_);
return v___x_2852_;
}
}
v___jp_2853_:
{
uint8_t v___x_2858_; 
v___x_2858_ = l_Lean_instBEqFVarId_beq(v___y_2856_, v___y_2855_);
lean_dec(v___y_2856_);
if (v___x_2858_ == 0)
{
lean_dec_ref(v___y_2857_);
v___y_2847_ = v___y_2854_;
v___y_2848_ = v___y_2855_;
v___y_2849_ = v___x_2858_;
goto v___jp_2846_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = lean_ptr_addr(v___y_2857_);
lean_dec_ref(v___y_2857_);
v___x_2860_ = lean_ptr_addr(v___y_2854_);
v___x_2861_ = lean_usize_dec_eq(v___x_2859_, v___x_2860_);
v___y_2847_ = v___y_2854_;
v___y_2848_ = v___y_2855_;
v___y_2849_ = v___x_2861_;
goto v___jp_2846_;
}
}
v___jp_2862_:
{
if (lean_obj_tag(v___y_2867_) == 0)
{
lean_dec_ref(v___y_2867_);
v___y_2854_ = v___y_2863_;
v___y_2855_ = v___y_2864_;
v___y_2856_ = v___y_2865_;
v___y_2857_ = v___y_2866_;
goto v___jp_2853_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v_code_2365_);
v_a_2868_ = lean_ctor_get(v___y_2867_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___y_2867_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___y_2867_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___y_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
v___jp_2876_:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2888_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___y_2877_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v___y_2877_);
v_a_2889_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2879_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2879_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
v___jp_2897_:
{
if (lean_obj_tag(v___y_2900_) == 0)
{
lean_dec_ref(v___y_2900_);
v___y_2877_ = v___y_2898_;
v___y_2878_ = v___y_2899_;
goto v___jp_2876_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___y_2898_);
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
uint8_t v___x_2919_; 
v___x_2919_ = lean_nat_dec_lt(v___y_2911_, v___y_2912_);
lean_dec(v___y_2911_);
if (v___x_2919_ == 0)
{
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2912_);
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_nat_dec_le(v___y_2912_, v___y_2912_);
if (v___x_2921_ == 0)
{
if (v___x_2919_ == 0)
{
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2912_);
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
goto v___jp_2876_;
}
else
{
size_t v___x_2922_; size_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = ((size_t)0ULL);
v___x_2923_ = lean_usize_of_nat(v___y_2912_);
lean_dec(v___y_2912_);
v___x_2924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2916_, v___x_2922_, v___x_2923_, v___x_2920_, v___y_2910_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v___y_2916_);
v___y_2898_ = v___y_2917_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2924_;
goto v___jp_2897_;
}
}
else
{
size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = ((size_t)0ULL);
v___x_2926_ = lean_usize_of_nat(v___y_2912_);
lean_dec(v___y_2912_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_2916_, v___x_2925_, v___x_2926_, v___x_2920_, v___y_2910_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v___y_2916_);
v___y_2898_ = v___y_2917_;
v___y_2899_ = v___y_2918_;
v___y_2900_ = v___x_2927_;
goto v___jp_2897_;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2933_, 0, v___y_2930_);
lean_ctor_set(v___x_2933_, 1, v___y_2932_);
lean_ctor_set(v___x_2933_, 2, v___y_2929_);
lean_ctor_set(v___x_2933_, 3, v___y_2931_);
v___x_2934_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
return v___x_2935_;
}
v___jp_2936_:
{
if (v___y_2942_ == 0)
{
lean_dec(v___y_2939_);
lean_dec_ref(v_code_2365_);
v___y_2929_ = v___y_2937_;
v___y_2930_ = v___y_2938_;
v___y_2931_ = v___y_2941_;
v___y_2932_ = v___y_2940_;
goto v___jp_2928_;
}
else
{
uint8_t v___x_2943_; 
v___x_2943_ = l_Lean_instBEqFVarId_beq(v___y_2939_, v___y_2937_);
lean_dec(v___y_2939_);
if (v___x_2943_ == 0)
{
lean_dec_ref(v_code_2365_);
v___y_2929_ = v___y_2937_;
v___y_2930_ = v___y_2938_;
v___y_2931_ = v___y_2941_;
v___y_2932_ = v___y_2940_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2944_; 
lean_dec_ref(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_code_2365_);
return v___x_2944_;
}
}
}
v___jp_2945_:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_array_get_size(v___y_2952_);
v___x_2960_ = lean_nat_dec_lt(v___y_2947_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v___y_2946_);
lean_dec_ref(v_code_2365_);
v___y_2910_ = v___y_2955_;
v___y_2911_ = v___y_2947_;
v___y_2912_ = v___x_2959_;
v___y_2913_ = v___y_2956_;
v___y_2914_ = v___y_2957_;
v___y_2915_ = v___y_2958_;
v___y_2916_ = v___y_2952_;
v___y_2917_ = v___y_2953_;
v___y_2918_ = v___y_2954_;
goto v___jp_2909_;
}
else
{
if (v___x_2960_ == 0)
{
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v___y_2946_);
lean_dec_ref(v_code_2365_);
v___y_2910_ = v___y_2955_;
v___y_2911_ = v___y_2947_;
v___y_2912_ = v___x_2959_;
v___y_2913_ = v___y_2956_;
v___y_2914_ = v___y_2957_;
v___y_2915_ = v___y_2958_;
v___y_2916_ = v___y_2952_;
v___y_2917_ = v___y_2953_;
v___y_2918_ = v___y_2954_;
goto v___jp_2909_;
}
else
{
size_t v___x_2961_; size_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = lean_usize_of_nat(v___x_2959_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_2952_, v___x_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v___y_2946_);
lean_dec_ref(v_code_2365_);
v___y_2910_ = v___y_2955_;
v___y_2911_ = v___y_2947_;
v___y_2912_ = v___x_2959_;
v___y_2913_ = v___y_2956_;
v___y_2914_ = v___y_2957_;
v___y_2915_ = v___y_2958_;
v___y_2916_ = v___y_2952_;
v___y_2917_ = v___y_2953_;
v___y_2918_ = v___y_2954_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2964_; 
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2947_);
lean_inc(v___y_2946_);
v___x_2964_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v___y_2946_, v___y_2954_);
if (lean_obj_tag(v___x_2964_) == 0)
{
size_t v___x_2965_; size_t v___x_2966_; uint8_t v___x_2967_; 
lean_dec_ref(v___x_2964_);
v___x_2965_ = lean_ptr_addr(v___y_2949_);
lean_dec_ref(v___y_2949_);
v___x_2966_ = lean_ptr_addr(v___y_2952_);
v___x_2967_ = lean_usize_dec_eq(v___x_2965_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v___y_2951_);
v___y_2937_ = v___y_2946_;
v___y_2938_ = v___y_2948_;
v___y_2939_ = v___y_2950_;
v___y_2940_ = v___y_2953_;
v___y_2941_ = v___y_2952_;
v___y_2942_ = v___x_2967_;
goto v___jp_2936_;
}
else
{
size_t v___x_2968_; size_t v___x_2969_; uint8_t v___x_2970_; 
v___x_2968_ = lean_ptr_addr(v___y_2951_);
lean_dec_ref(v___y_2951_);
v___x_2969_ = lean_ptr_addr(v___y_2953_);
v___x_2970_ = lean_usize_dec_eq(v___x_2968_, v___x_2969_);
v___y_2937_ = v___y_2946_;
v___y_2938_ = v___y_2948_;
v___y_2939_ = v___y_2950_;
v___y_2940_ = v___y_2953_;
v___y_2941_ = v___y_2952_;
v___y_2942_ = v___x_2970_;
goto v___jp_2936_;
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v___y_2946_);
lean_dec_ref(v_code_2365_);
v_a_2971_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2964_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2964_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
}
v___jp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2367_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2989_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___y_2980_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___y_2980_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v___y_2980_);
v_a_2990_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2981_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
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
v___jp_2998_:
{
if (lean_obj_tag(v___y_3000_) == 0)
{
lean_dec_ref(v___y_3000_);
v___y_2980_ = v___y_2999_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref(v___y_2999_);
v_a_3001_ = lean_ctor_get(v___y_3000_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___y_3000_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___y_3000_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___y_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
v___jp_3009_:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_nat_dec_lt(v___y_3010_, v___y_3013_);
lean_dec(v___y_3010_);
if (v___x_3014_ == 0)
{
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3011_);
v___y_2980_ = v___y_3012_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_nat_dec_le(v___y_3013_, v___y_3013_);
if (v___x_3016_ == 0)
{
if (v___x_3014_ == 0)
{
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3011_);
v___y_2980_ = v___y_3012_;
goto v___jp_2979_;
}
else
{
size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = lean_usize_of_nat(v___y_3013_);
lean_dec(v___y_3013_);
v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3011_, v___x_3017_, v___x_3018_, v___x_3015_, v_a_2370_);
lean_dec_ref(v___y_3011_);
v___y_2999_ = v___y_3012_;
v___y_3000_ = v___x_3019_;
goto v___jp_2998_;
}
}
else
{
size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = lean_usize_of_nat(v___y_3013_);
lean_dec(v___y_3013_);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_3011_, v___x_3020_, v___x_3021_, v___x_3015_, v_a_2370_);
lean_dec_ref(v___y_3011_);
v___y_2999_ = v___y_3012_;
v___y_3000_ = v___x_3022_;
goto v___jp_2998_;
}
}
}
v___jp_3039_:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2367_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3266_; 
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3267_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3266_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3266_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_add(v_currRecDepth_3026_, v___x_3044_);
lean_dec(v_currRecDepth_3026_);
v___x_3046_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3046_, 0, v_fileName_3023_);
lean_ctor_set(v___x_3046_, 1, v_fileMap_3024_);
lean_ctor_set(v___x_3046_, 2, v_options_3025_);
lean_ctor_set(v___x_3046_, 3, v___x_3045_);
lean_ctor_set(v___x_3046_, 4, v_maxRecDepth_3027_);
lean_ctor_set(v___x_3046_, 5, v_ref_3028_);
lean_ctor_set(v___x_3046_, 6, v_currNamespace_3029_);
lean_ctor_set(v___x_3046_, 7, v_openDecls_3030_);
lean_ctor_set(v___x_3046_, 8, v_initHeartbeats_3031_);
lean_ctor_set(v___x_3046_, 9, v_maxHeartbeats_3032_);
lean_ctor_set(v___x_3046_, 10, v_quotContext_3033_);
lean_ctor_set(v___x_3046_, 11, v_currMacroScope_3034_);
lean_ctor_set(v___x_3046_, 12, v_cancelTk_x3f_3036_);
lean_ctor_set(v___x_3046_, 13, v_inheritedTraceOptions_3038_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*14, v_diag_3035_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*14 + 1, v_suppressElabErrors_3037_);
switch(lean_obj_tag(v_code_2365_))
{
case 0:
{
lean_object* v_decl_3047_; lean_object* v_k_3048_; uint8_t v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; 
lean_del_object(v___x_3042_);
v_decl_3047_ = lean_ctor_get(v_code_2365_, 0);
v_k_3048_ = lean_ctor_get(v_code_2365_, 1);
v___x_3049_ = 0;
v___x_3050_ = 0;
lean_inc_ref(v_decl_3047_);
v___x_3051_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_3049_, v___x_3050_, v_decl_3047_, v_a_2367_, v_a_2370_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; uint8_t v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___x_3051_);
v___x_3053_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_3049_, v_decl_3047_, v_a_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2367_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_dec_ref(v___x_3054_);
lean_inc_ref(v_k_3048_);
lean_inc_ref(v_decl_3047_);
v___y_2799_ = v_decl_3047_;
v___y_2800_ = v_a_3052_;
v___y_2801_ = v___x_3049_;
v___y_2802_ = v_k_3048_;
v___y_2803_ = v_a_2366_;
v___y_2804_ = v_a_2367_;
v___y_2805_ = v_a_2368_;
v___y_2806_ = v_a_2369_;
v___y_2807_ = v_a_2370_;
v___y_2808_ = v___x_3046_;
v___y_2809_ = v_a_2372_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_3052_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_inc_ref(v_k_3048_);
lean_inc_ref(v_decl_3047_);
v___y_2799_ = v_decl_3047_;
v___y_2800_ = v_a_3052_;
v___y_2801_ = v___x_3049_;
v___y_2802_ = v_k_3048_;
v___y_2803_ = v_a_2366_;
v___y_2804_ = v_a_2367_;
v___y_2805_ = v_a_2368_;
v___y_2806_ = v_a_2369_;
v___y_2807_ = v_a_2370_;
v___y_2808_ = v___x_3046_;
v___y_2809_ = v_a_2372_;
goto v___jp_2798_;
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3063_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3051_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3051_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_3071_; lean_object* v_args_3072_; lean_object* v___x_3073_; lean_object* v_subst_3074_; uint8_t v___x_3075_; uint8_t v___x_3076_; lean_object* v___x_3077_; 
lean_del_object(v___x_3042_);
v_fvarId_3071_ = lean_ctor_get(v_code_2365_, 0);
v_args_3072_ = lean_ctor_get(v_code_2365_, 1);
v___x_3073_ = lean_st_ref_get(v_a_2367_);
v_subst_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc_ref(v_subst_3074_);
lean_dec(v___x_3073_);
v___x_3075_ = 0;
v___x_3076_ = 0;
lean_inc(v_fvarId_3071_);
v___x_3077_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3074_, v_fvarId_3071_, v___x_3076_);
lean_dec_ref(v_subst_3074_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_fvarId_3078_; lean_object* v___x_3079_; 
v_fvarId_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_fvarId_3078_);
lean_dec_ref(v___x_3077_);
lean_inc_ref(v_args_3072_);
v___x_3079_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_3075_, v___x_3076_, v_args_3072_, v_a_2367_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc_n(v_a_3080_, 2);
lean_dec_ref(v___x_3079_);
v___x_3081_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_3078_, v_a_3080_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
if (lean_obj_tag(v_a_3082_) == 1)
{
lean_object* v_val_3083_; 
lean_dec(v_a_3080_);
lean_dec(v_fvarId_3078_);
lean_dec_ref(v_code_2365_);
v_val_3083_ = lean_ctor_get(v_a_3082_, 0);
lean_inc(v_val_3083_);
lean_dec_ref(v_a_3082_);
v_code_2365_ = v_val_3083_;
v_a_2371_ = v___x_3046_;
goto _start;
}
else
{
lean_object* v___x_3085_; 
lean_dec(v_a_3082_);
lean_dec_ref(v___x_3046_);
lean_inc(v_fvarId_3078_);
v___x_3085_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3078_, v_a_2367_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
lean_dec_ref(v___x_3085_);
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = lean_array_get_size(v_a_3080_);
v___x_3088_ = lean_nat_dec_lt(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_inc_ref(v_args_3072_);
lean_inc(v_fvarId_3071_);
v___y_2854_ = v_a_3080_;
v___y_2855_ = v_fvarId_3078_;
v___y_2856_ = v_fvarId_3071_;
v___y_2857_ = v_args_3072_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_nat_dec_le(v___x_3087_, v___x_3087_);
if (v___x_3090_ == 0)
{
if (v___x_3088_ == 0)
{
lean_inc_ref(v_args_3072_);
lean_inc(v_fvarId_3071_);
v___y_2854_ = v_a_3080_;
v___y_2855_ = v_fvarId_3078_;
v___y_2856_ = v_fvarId_3071_;
v___y_2857_ = v_args_3072_;
goto v___jp_2853_;
}
else
{
size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = lean_usize_of_nat(v___x_3087_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3080_, v___x_3091_, v___x_3092_, v___x_3089_, v_a_2367_);
lean_inc_ref(v_args_3072_);
lean_inc(v_fvarId_3071_);
v___y_2863_ = v_a_3080_;
v___y_2864_ = v_fvarId_3078_;
v___y_2865_ = v_fvarId_3071_;
v___y_2866_ = v_args_3072_;
v___y_2867_ = v___x_3093_;
goto v___jp_2862_;
}
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = lean_usize_of_nat(v___x_3087_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_3080_, v___x_3094_, v___x_3095_, v___x_3089_, v_a_2367_);
lean_inc_ref(v_args_3072_);
lean_inc(v_fvarId_3071_);
v___y_2863_ = v_a_3080_;
v___y_2864_ = v_fvarId_3078_;
v___y_2865_ = v_fvarId_3071_;
v___y_2866_ = v_args_3072_;
v___y_2867_ = v___x_3096_;
goto v___jp_2862_;
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_a_3080_);
lean_dec(v_fvarId_3078_);
lean_dec_ref(v_code_2365_);
v_a_3097_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3085_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3085_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3080_);
lean_dec(v_fvarId_3078_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3105_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3081_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3081_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_fvarId_3078_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3113_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3079_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3079_);
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
else
{
lean_object* v___x_3121_; 
lean_dec_ref(v_code_2365_);
v___x_3121_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3075_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
lean_dec_ref(v___x_3046_);
return v___x_3121_;
}
}
case 4:
{
lean_object* v_cases_3122_; lean_object* v___x_3123_; 
lean_del_object(v___x_3042_);
v_cases_3122_ = lean_ctor_get(v_code_2365_, 0);
lean_inc_ref(v_cases_3122_);
v___x_3123_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3122_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3195_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3195_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3195_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
if (lean_obj_tag(v_a_3124_) == 1)
{
lean_object* v_val_3128_; lean_object* v___x_3130_; 
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_val_3128_ = lean_ctor_get(v_a_3124_, 0);
lean_inc(v_val_3128_);
lean_dec_ref(v_a_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v_val_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_val_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
else
{
lean_object* v_typeName_3132_; lean_object* v_resultType_3133_; lean_object* v_discr_3134_; lean_object* v_alts_3135_; lean_object* v___x_3136_; lean_object* v_subst_3137_; uint8_t v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; 
lean_del_object(v___x_3126_);
lean_dec(v_a_3124_);
v_typeName_3132_ = lean_ctor_get(v_cases_3122_, 0);
v_resultType_3133_ = lean_ctor_get(v_cases_3122_, 1);
v_discr_3134_ = lean_ctor_get(v_cases_3122_, 2);
v_alts_3135_ = lean_ctor_get(v_cases_3122_, 3);
v___x_3136_ = lean_st_ref_get(v_a_2367_);
v_subst_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc_ref(v_subst_3137_);
lean_dec(v___x_3136_);
v___x_3138_ = 0;
v___x_3139_ = 0;
lean_inc(v_discr_3134_);
v___x_3140_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3137_, v_discr_3134_, v___x_3139_);
lean_dec_ref(v_subst_3137_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_fvarId_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_fvarId_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc_n(v_fvarId_3141_, 2);
lean_dec_ref(v___x_3140_);
v___x_3142_ = lean_st_ref_get(v_a_2367_);
v___x_3143_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3135_);
v___x_3144_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3141_, v___x_3143_, v_alts_3135_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3145_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3177_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_subst_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_subst_3151_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_subst_3151_);
lean_dec(v___x_3142_);
lean_inc_ref(v_resultType_3133_);
v___x_3152_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3138_, v_subst_3151_, v___x_3139_, v_resultType_3133_);
lean_dec_ref(v_subst_3151_);
v___x_3153_ = lean_array_get_size(v_a_3147_);
v___x_3154_ = lean_nat_dec_eq(v___x_3153_, v___x_3044_);
if (v___x_3154_ == 0)
{
lean_del_object(v___x_3149_);
lean_inc_ref(v_resultType_3133_);
lean_inc(v_discr_3134_);
lean_inc_ref(v_alts_3135_);
lean_inc(v_typeName_3132_);
v___y_2946_ = v_fvarId_3141_;
v___y_2947_ = v___x_3143_;
v___y_2948_ = v_typeName_3132_;
v___y_2949_ = v_alts_3135_;
v___y_2950_ = v_discr_3134_;
v___y_2951_ = v_resultType_3133_;
v___y_2952_ = v_a_3147_;
v___y_2953_ = v___x_3152_;
v___y_2954_ = v_a_2367_;
v___y_2955_ = v_a_2369_;
v___y_2956_ = v_a_2370_;
v___y_2957_ = v___x_3046_;
v___y_2958_ = v_a_2372_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_array_fget_borrowed(v_a_3147_, v___x_3143_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_params_3156_; lean_object* v_code_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
lean_del_object(v___x_3149_);
v_params_3156_ = lean_ctor_get(v___x_3155_, 1);
v_code_3157_ = lean_ctor_get(v___x_3155_, 2);
v___x_3158_ = lean_array_get_size(v_params_3156_);
v___x_3159_ = lean_nat_dec_lt(v___x_3143_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_inc_ref(v_code_3157_);
lean_inc_ref(v_params_3156_);
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3147_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v___y_3010_ = v___x_3143_;
v___y_3011_ = v_params_3156_;
v___y_3012_ = v_code_3157_;
v___y_3013_ = v___x_3158_;
goto v___jp_3009_;
}
else
{
if (v___x_3159_ == 0)
{
lean_inc_ref(v_code_3157_);
lean_inc_ref(v_params_3156_);
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3147_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v___y_3010_ = v___x_3143_;
v___y_3011_ = v_params_3156_;
v___y_3012_ = v_code_3157_;
v___y_3013_ = v___x_3158_;
goto v___jp_3009_;
}
else
{
size_t v___x_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = ((size_t)0ULL);
v___x_3161_ = lean_usize_of_nat(v___x_3158_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3156_, v___x_3160_, v___x_3161_, v_a_2367_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; uint8_t v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = lean_unbox(v_a_3163_);
lean_dec(v_a_3163_);
if (v___x_3164_ == 0)
{
lean_inc_ref(v_code_3157_);
lean_inc_ref(v_params_3156_);
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3147_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v___y_3010_ = v___x_3143_;
v___y_3011_ = v_params_3156_;
v___y_3012_ = v_code_3157_;
v___y_3013_ = v___x_3158_;
goto v___jp_3009_;
}
else
{
lean_inc_ref(v_resultType_3133_);
lean_inc(v_discr_3134_);
lean_inc_ref(v_alts_3135_);
lean_inc(v_typeName_3132_);
v___y_2946_ = v_fvarId_3141_;
v___y_2947_ = v___x_3143_;
v___y_2948_ = v_typeName_3132_;
v___y_2949_ = v_alts_3135_;
v___y_2950_ = v_discr_3134_;
v___y_2951_ = v_resultType_3133_;
v___y_2952_ = v_a_3147_;
v___y_2953_ = v___x_3152_;
v___y_2954_ = v_a_2367_;
v___y_2955_ = v_a_2369_;
v___y_2956_ = v_a_2370_;
v___y_2957_ = v___x_3046_;
v___y_2958_ = v_a_2372_;
goto v___jp_2945_;
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3147_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3165_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3162_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3162_);
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
}
}
else
{
lean_object* v_code_3173_; lean_object* v___x_3175_; 
lean_inc_ref(v___x_3155_);
lean_dec_ref(v___x_3152_);
lean_dec(v_a_3147_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_code_3173_ = lean_ctor_get(v___x_3155_, 0);
lean_inc_ref(v_code_3173_);
lean_dec_ref(v___x_3155_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v_code_3173_);
v___x_3175_ = v___x_3149_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_code_3173_);
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
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v___x_3142_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3178_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3146_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3146_);
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
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v___x_3142_);
lean_dec(v_fvarId_3141_);
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3186_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3144_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3144_);
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
else
{
lean_object* v___x_3194_; 
lean_dec_ref(v_code_2365_);
v___x_3194_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3138_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
lean_dec_ref(v___x_3046_);
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_code_2365_);
lean_dec_ref(v___x_3046_);
v_a_3196_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3123_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3123_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
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
case 5:
{
lean_object* v_fvarId_3204_; lean_object* v___x_3205_; lean_object* v_subst_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; 
lean_del_object(v___x_3042_);
v_fvarId_3204_ = lean_ctor_get(v_code_2365_, 0);
v___x_3205_ = lean_st_ref_get(v_a_2367_);
v_subst_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc_ref(v_subst_3206_);
lean_dec(v___x_3205_);
v___x_3207_ = 0;
lean_inc(v_fvarId_3204_);
v___x_3208_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3206_, v_fvarId_3204_, v___x_3207_);
lean_dec_ref(v_subst_3206_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_fvarId_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v___x_3046_);
v_fvarId_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_n(v_fvarId_3209_, 2);
lean_dec_ref(v___x_3208_);
v___x_3210_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3209_, v_a_2367_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3229_; 
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3230_);
v___x_3212_ = v___x_3210_;
v_isShared_3213_ = v_isSharedCheck_3229_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v___x_3210_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3229_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
uint8_t v___x_3214_; 
v___x_3214_ = l_Lean_instBEqFVarId_beq(v_fvarId_3204_, v_fvarId_3209_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3224_; 
v_isSharedCheck_3224_ = !lean_is_exclusive(v_code_2365_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v_code_2365_, 0);
lean_dec(v_unused_3225_);
v___x_3216_ = v_code_2365_;
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
else
{
lean_dec(v_code_2365_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v_fvarId_3209_);
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_fvarId_3209_);
v___x_3219_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3221_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3219_);
v___x_3221_ = v___x_3212_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
lean_object* v___x_3227_; 
lean_dec(v_fvarId_3209_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_code_2365_);
v___x_3227_ = v___x_3212_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_code_2365_);
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
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_fvarId_3209_);
lean_dec_ref(v_code_2365_);
v_a_3231_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3210_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3210_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
uint8_t v___x_3239_; lean_object* v___x_3240_; 
lean_dec_ref(v_code_2365_);
v___x_3239_ = 0;
v___x_3240_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3239_, v_a_2369_, v_a_2370_, v___x_3046_, v_a_2372_);
lean_dec_ref(v___x_3046_);
return v___x_3240_;
}
}
case 6:
{
lean_object* v_type_3241_; lean_object* v___x_3242_; lean_object* v_subst_3243_; uint8_t v___x_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; size_t v___x_3247_; size_t v___x_3248_; uint8_t v___x_3249_; 
lean_dec_ref(v___x_3046_);
v_type_3241_ = lean_ctor_get(v_code_2365_, 0);
v___x_3242_ = lean_st_ref_get(v_a_2367_);
v_subst_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_subst_3243_);
lean_dec(v___x_3242_);
v___x_3244_ = 0;
v___x_3245_ = 0;
lean_inc_ref(v_type_3241_);
v___x_3246_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3244_, v_subst_3243_, v___x_3245_, v_type_3241_);
lean_dec_ref(v_subst_3243_);
v___x_3247_ = lean_ptr_addr(v_type_3241_);
v___x_3248_ = lean_ptr_addr(v___x_3246_);
v___x_3249_ = lean_usize_dec_eq(v___x_3247_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3259_; 
v_isSharedCheck_3259_ = !lean_is_exclusive(v_code_2365_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v_code_2365_, 0);
lean_dec(v_unused_3260_);
v___x_3251_ = v_code_2365_;
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v_code_2365_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3246_);
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3246_);
v___x_3254_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3256_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3254_);
v___x_3256_ = v___x_3042_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
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
lean_object* v___x_3262_; 
lean_dec_ref(v___x_3246_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v_code_2365_);
v___x_3262_ = v___x_3042_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_code_2365_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
default: 
{
lean_object* v_decl_3264_; lean_object* v_k_3265_; 
lean_del_object(v___x_3042_);
v_decl_3264_ = lean_ctor_get(v_code_2365_, 0);
v_k_3265_ = lean_ctor_get(v_code_2365_, 1);
lean_inc_ref(v_k_3265_);
lean_inc_ref(v_decl_3264_);
v_decl_2483_ = v_decl_3264_;
v_k_2484_ = v_k_3265_;
v___y_2485_ = v_a_2366_;
v___y_2486_ = v_a_2367_;
v___y_2487_ = v_a_2368_;
v___y_2488_ = v_a_2369_;
v___y_2489_ = v_a_2370_;
v___y_2490_ = v___x_3046_;
v___y_2491_ = v_a_2372_;
goto v___jp_2482_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_inheritedTraceOptions_3038_);
lean_dec(v_cancelTk_x3f_3036_);
lean_dec(v_currMacroScope_3034_);
lean_dec(v_quotContext_3033_);
lean_dec(v_maxHeartbeats_3032_);
lean_dec(v_initHeartbeats_3031_);
lean_dec(v_openDecls_3030_);
lean_dec(v_currNamespace_3029_);
lean_dec(v_ref_3028_);
lean_dec(v_maxRecDepth_3027_);
lean_dec(v_currRecDepth_3026_);
lean_dec_ref(v_options_3025_);
lean_dec_ref(v_fileMap_3024_);
lean_dec_ref(v_fileName_3023_);
lean_dec_ref(v_code_2365_);
v_a_3268_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3040_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3040_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_params_3289_; lean_object* v_type_3290_; lean_object* v_value_3291_; lean_object* v___x_3292_; lean_object* v_subst_3293_; uint8_t v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_params_3289_ = lean_ctor_get(v_decl_3280_, 2);
v_type_3290_ = lean_ctor_get(v_decl_3280_, 3);
v_value_3291_ = lean_ctor_get(v_decl_3280_, 4);
v___x_3292_ = lean_st_ref_get(v_a_3282_);
v_subst_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_subst_3293_);
lean_dec(v___x_3292_);
v___x_3294_ = 0;
v___x_3295_ = 0;
lean_inc_ref(v_type_3290_);
v___x_3296_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3294_, v_subst_3293_, v___x_3295_, v_type_3290_);
lean_dec_ref(v_subst_3293_);
lean_inc_ref(v_params_3289_);
v___x_3297_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3294_, v___x_3295_, v_params_3289_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
lean_inc_ref(v_a_3286_);
lean_inc_ref(v_value_3291_);
v___x_3299_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3291_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3294_, v_decl_3280_, v___x_3296_, v_a_3298_, v_a_3300_, v_a_3285_);
return v___x_3301_;
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3298_);
lean_dec_ref(v___x_3296_);
lean_dec_ref(v_decl_3280_);
v_a_3302_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3299_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3299_);
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
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v___x_3296_);
lean_dec_ref(v_decl_3280_);
v_a_3310_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3297_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3297_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* v_decl_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3328_, lean_object* v_i_3329_, lean_object* v_as_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3328_, v_i_3329_, v_as_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3350_, lean_object* v_k_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3350_, v_k_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec_ref(v_a_3354_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3371_, uint8_t v_t_3372_, lean_object* v_decl_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3371_, v_t_3372_, v_decl_3373_, v___y_3375_, v___y_3378_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3383_, lean_object* v_t_3384_, lean_object* v_decl_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_pu_boxed_3394_; uint8_t v_t_boxed_3395_; lean_object* v_res_3396_; 
v_pu_boxed_3394_ = lean_unbox(v_pu_3383_);
v_t_boxed_3395_ = lean_unbox(v_t_3384_);
v_res_3396_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3394_, v_t_boxed_3395_, v_decl_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3397_, uint8_t v_t_3398_, lean_object* v_args_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3397_, v_t_3398_, v_args_3399_, v___y_3401_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3409_, lean_object* v_t_3410_, lean_object* v_args_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
uint8_t v_pu_boxed_3420_; uint8_t v_t_boxed_3421_; lean_object* v_res_3422_; 
v_pu_boxed_3420_ = lean_unbox(v_pu_3409_);
v_t_boxed_3421_ = lean_unbox(v_t_3410_);
v_res_3422_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3420_, v_t_boxed_3421_, v_args_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3423_, lean_object* v_R_3424_, lean_object* v_a_3425_, lean_object* v_b_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3425_, v_b_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3429_, v_x_3430_, v_x_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3433_, size_t v_i_3434_, size_t v_stop_3435_, lean_object* v_b_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3433_, v_i_3434_, v_stop_3435_, v_b_3436_, v___y_3438_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3446_, lean_object* v_i_3447_, lean_object* v_stop_3448_, lean_object* v_b_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
size_t v_i_boxed_3458_; size_t v_stop_boxed_3459_; lean_object* v_res_3460_; 
v_i_boxed_3458_ = lean_unbox_usize(v_i_3447_);
lean_dec(v_i_3447_);
v_stop_boxed_3459_ = lean_unbox_usize(v_stop_3448_);
lean_dec(v_stop_3448_);
v_res_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3446_, v_i_boxed_3458_, v_stop_boxed_3459_, v_b_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_as_3446_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3461_, size_t v_i_3462_, size_t v_stop_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3461_, v_i_3462_, v_stop_3463_, v___y_3470_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3473_, lean_object* v_i_3474_, lean_object* v_stop_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
size_t v_i_boxed_3484_; size_t v_stop_boxed_3485_; lean_object* v_res_3486_; 
v_i_boxed_3484_ = lean_unbox_usize(v_i_3474_);
lean_dec(v_i_3474_);
v_stop_boxed_3485_ = lean_unbox_usize(v_stop_3475_);
lean_dec(v_stop_3475_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3473_, v_i_boxed_3484_, v_stop_boxed_3485_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_as_3473_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3487_, size_t v_i_3488_, size_t v_stop_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3487_, v_i_3488_, v_stop_3489_, v_b_3490_, v___y_3492_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3497_, lean_object* v_i_3498_, lean_object* v_stop_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
size_t v_i_boxed_3506_; size_t v_stop_boxed_3507_; lean_object* v_res_3508_; 
v_i_boxed_3506_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_stop_boxed_3507_ = lean_unbox_usize(v_stop_3499_);
lean_dec(v_stop_3499_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3497_, v_i_boxed_3506_, v_stop_boxed_3507_, v_b_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_as_3497_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3509_, size_t v_i_3510_, size_t v_stop_3511_, lean_object* v_b_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3509_, v_i_3510_, v_stop_3511_, v_b_3512_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3522_, lean_object* v_i_3523_, lean_object* v_stop_3524_, lean_object* v_b_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_i_boxed_3534_; size_t v_stop_boxed_3535_; lean_object* v_res_3536_; 
v_i_boxed_3534_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_stop_boxed_3535_ = lean_unbox_usize(v_stop_3524_);
lean_dec(v_stop_3524_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3522_, v_i_boxed_3534_, v_stop_boxed_3535_, v_b_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v_as_3522_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3537_, size_t v_i_3538_, size_t v_stop_3539_, lean_object* v_b_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3537_, v_i_3538_, v_stop_3539_, v_b_3540_, v___y_3545_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3550_, lean_object* v_i_3551_, lean_object* v_stop_3552_, lean_object* v_b_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
size_t v_i_boxed_3562_; size_t v_stop_boxed_3563_; lean_object* v_res_3564_; 
v_i_boxed_3562_ = lean_unbox_usize(v_i_3551_);
lean_dec(v_i_3551_);
v_stop_boxed_3563_ = lean_unbox_usize(v_stop_3552_);
lean_dec(v_stop_3552_);
v_res_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3550_, v_i_boxed_3562_, v_stop_boxed_3563_, v_b_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v_as_3550_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3565_, size_t v_i_3566_, size_t v_stop_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3565_, v_i_3566_, v_stop_3567_, v___y_3569_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3577_, lean_object* v_i_3578_, lean_object* v_stop_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_i_boxed_3588_; size_t v_stop_boxed_3589_; lean_object* v_res_3590_; 
v_i_boxed_3588_ = lean_unbox_usize(v_i_3578_);
lean_dec(v_i_3578_);
v_stop_boxed_3589_ = lean_unbox_usize(v_stop_3579_);
lean_dec(v_stop_3579_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3577_, v_i_boxed_3588_, v_stop_boxed_3589_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v_as_3577_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3591_, size_t v_sz_3592_, size_t v_i_3593_, lean_object* v_b_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3591_, v_sz_3592_, v_i_3593_, v_b_3594_, v___y_3596_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3604_, lean_object* v_sz_3605_, lean_object* v_i_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
size_t v_sz_boxed_3616_; size_t v_i_boxed_3617_; lean_object* v_res_3618_; 
v_sz_boxed_3616_ = lean_unbox_usize(v_sz_3605_);
lean_dec(v_sz_3605_);
v_i_boxed_3617_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_res_3618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3604_, v_sz_boxed_3616_, v_i_boxed_3617_, v_b_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3619_, lean_object* v_x_3620_, size_t v_x_3621_, size_t v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3620_, v_x_3621_, v_x_3622_, v_x_3623_, v_x_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3626_, lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
size_t v_x_48962__boxed_3632_; size_t v_x_48963__boxed_3633_; lean_object* v_res_3634_; 
v_x_48962__boxed_3632_ = lean_unbox_usize(v_x_3628_);
lean_dec(v_x_3628_);
v_x_48963__boxed_3633_ = lean_unbox_usize(v_x_3629_);
lean_dec(v_x_3629_);
v_res_3634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3626_, v_x_3627_, v_x_48962__boxed_3632_, v_x_48963__boxed_3633_, v_x_3630_, v_x_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3635_, uint8_t v_t_3636_, lean_object* v_i_3637_, lean_object* v_as_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3635_, v_t_3636_, v_i_3637_, v_as_3638_, v___y_3640_, v___y_3643_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3648_, lean_object* v_t_3649_, lean_object* v_i_3650_, lean_object* v_as_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v_pu_boxed_3660_; uint8_t v_t_boxed_3661_; lean_object* v_res_3662_; 
v_pu_boxed_3660_ = lean_unbox(v_pu_3648_);
v_t_boxed_3661_ = lean_unbox(v_t_3649_);
v_res_3662_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3660_, v_t_boxed_3661_, v_i_3650_, v_as_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3663_, lean_object* v_n_3664_, lean_object* v_k_3665_, lean_object* v_v_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3664_, v_k_3665_, v_v_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3668_, size_t v_depth_3669_, lean_object* v_keys_3670_, lean_object* v_vals_3671_, lean_object* v_heq_3672_, lean_object* v_i_3673_, lean_object* v_entries_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3669_, v_keys_3670_, v_vals_3671_, v_i_3673_, v_entries_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3676_, lean_object* v_depth_3677_, lean_object* v_keys_3678_, lean_object* v_vals_3679_, lean_object* v_heq_3680_, lean_object* v_i_3681_, lean_object* v_entries_3682_){
_start:
{
size_t v_depth_boxed_3683_; lean_object* v_res_3684_; 
v_depth_boxed_3683_ = lean_unbox_usize(v_depth_3677_);
lean_dec(v_depth_3677_);
v_res_3684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3676_, v_depth_boxed_3683_, v_keys_3678_, v_vals_3679_, v_heq_3680_, v_i_3681_, v_entries_3682_);
lean_dec_ref(v_vals_3679_);
lean_dec_ref(v_keys_3678_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3685_, lean_object* v_x_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3686_, v_x_3687_, v_x_3688_, v_x_3689_);
return v___x_3690_;
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
