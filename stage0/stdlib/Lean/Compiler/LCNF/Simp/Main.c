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
v___y_996_ = v_code_998_;
goto v___jp_995_;
}
case 1:
{
lean_object* v_code_999_; 
v_code_999_ = lean_ctor_get(v___x_997_, 1);
v___y_996_ = v_code_999_;
goto v___jp_995_;
}
default: 
{
lean_object* v_code_1000_; 
v_code_1000_ = lean_ctor_get(v___x_997_, 0);
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
goto v___jp_991_;
}
else
{
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
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1109_);
v___x_1118_ = lean_apply_9(v___f_1108_, v_fvarId_1111_, v___y_1109_, v___y_1107_, v___y_1110_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
return v___x_1118_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_fvarId_1111_);
lean_dec_ref(v___f_1108_);
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
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1127_);
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
size_t v_x_44427__boxed_1290_; size_t v_x_44428__boxed_1291_; lean_object* v_res_1292_; 
v_x_44427__boxed_1290_ = lean_unbox_usize(v_x_1286_);
lean_dec(v_x_1286_);
v_x_44428__boxed_1291_ = lean_unbox_usize(v_x_1287_);
lean_dec(v_x_1287_);
v_res_1292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_1285_, v_x_44427__boxed_1290_, v_x_44428__boxed_1291_, v_x_1288_, v_x_1289_);
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
v___x_1407_ = lean_panic_fn_borrowed(v___x_1406_, v_msg_1405_);
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
v___x_1545_ = lean_unsigned_to_nat(640u);
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
lean_inc_ref(v___y_1565_);
v___x_1599_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_1555_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1599_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
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
lean_inc_ref(v___y_1565_);
v___x_1580_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1579_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1580_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1576_);
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
uint8_t v___x_44957__boxed_1625_; lean_object* v_res_1626_; 
v___x_44957__boxed_1625_ = lean_unbox(v___x_1614_);
v_res_1626_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(v___x_1609_, v___x_1610_, v_fvarId_1611_, v_k_1612_, v_args_1613_, v___x_44957__boxed_1625_, v___x_1615_, v_result_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* v_letDecl_1627_, lean_object* v_k_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_fvarId_1637_; lean_object* v_value_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1976_; 
v_fvarId_1637_ = lean_ctor_get(v_letDecl_1627_, 0);
v_value_1638_ = lean_ctor_get(v_letDecl_1627_, 3);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_letDecl_1627_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; lean_object* v_unused_1978_; 
v_unused_1977_ = lean_ctor_get(v_letDecl_1627_, 2);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_letDecl_1627_, 1);
lean_dec(v_unused_1978_);
v___x_1640_ = v_letDecl_1627_;
v_isShared_1641_ = v_isSharedCheck_1976_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_value_1638_);
lean_inc(v_fvarId_1637_);
lean_dec(v_letDecl_1627_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1976_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; 
lean_inc(v_value_1638_);
v___x_1642_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(v_value_1638_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1967_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1967_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1967_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
if (lean_obj_tag(v_a_1643_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1645_);
v_val_1647_ = lean_ctor_get(v_a_1643_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1643_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1649_ = v_a_1643_;
v_isShared_1650_ = v_isSharedCheck_1962_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_val_1647_);
lean_dec(v_a_1643_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1962_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_params_1651_; lean_object* v_value_1652_; lean_object* v_fType_1653_; lean_object* v_args_1654_; uint8_t v_recursive_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; uint8_t v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; 
v_params_1651_ = lean_ctor_get(v_val_1647_, 0);
v_value_1652_ = lean_ctor_get(v_val_1647_, 1);
v_fType_1653_ = lean_ctor_get(v_val_1647_, 2);
v_args_1654_ = lean_ctor_get(v_val_1647_, 3);
v_recursive_1655_ = lean_ctor_get_uint8(v_val_1647_, sizeof(void*)*4 + 2);
v___x_1656_ = lean_array_get_size(v_args_1654_);
v___x_1657_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_1647_);
v___x_1658_ = lean_nat_dec_lt(v___x_1656_, v___x_1657_);
if (lean_obj_tag(v_value_1638_) == 3)
{
lean_object* v_declName_1942_; lean_object* v___x_1943_; 
v_declName_1942_ = lean_ctor_get(v_value_1638_, 0);
lean_inc_n(v_declName_1942_, 2);
lean_dec_ref(v_value_1638_);
v___x_1943_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1655_, v_declName_1942_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_declName_1945_; lean_object* v_config_1946_; lean_object* v_inlineStack_1947_; lean_object* v_inlineStackOccs_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v_declName_1945_ = lean_ctor_get(v_a_1629_, 0);
v_config_1946_ = lean_ctor_get(v_a_1629_, 1);
v_inlineStack_1947_ = lean_ctor_get(v_a_1629_, 2);
v_inlineStackOccs_1948_ = lean_ctor_get(v_a_1629_, 3);
lean_inc(v_inlineStack_1947_);
lean_inc(v_declName_1942_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_declName_1942_);
lean_ctor_set(v___x_1949_, 1, v_inlineStack_1947_);
lean_inc_ref(v_inlineStackOccs_1948_);
v___x_1950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_1948_, v_declName_1942_, v_a_1944_);
lean_inc_ref(v_config_1946_);
lean_inc(v_declName_1945_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 3, v___x_1950_);
lean_ctor_set(v___x_1640_, 2, v___x_1949_);
lean_ctor_set(v___x_1640_, 1, v_config_1946_);
lean_ctor_set(v___x_1640_, 0, v_declName_1945_);
v___x_1952_ = v___x_1640_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_declName_1945_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_config_1946_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
v___y_1841_ = v___x_1952_;
v___y_1842_ = v_a_1630_;
v___y_1843_ = v_a_1631_;
v___y_1844_ = v_a_1632_;
v___y_1845_ = v_a_1633_;
v___y_1846_ = v_a_1634_;
v___y_1847_ = v_a_1635_;
goto v___jp_1840_;
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_declName_1942_);
lean_dec(v___x_1657_);
lean_del_object(v___x_1649_);
lean_dec(v_val_1647_);
lean_del_object(v___x_1640_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1954_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1943_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1943_);
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
else
{
lean_del_object(v___x_1640_);
lean_dec(v_value_1638_);
lean_inc_ref(v_a_1629_);
v___y_1841_ = v_a_1629_;
v___y_1842_ = v_a_1630_;
v___y_1843_ = v_a_1631_;
v___y_1844_ = v_a_1632_;
v___y_1845_ = v_a_1633_;
v___y_1846_ = v_a_1634_;
v___y_1847_ = v_a_1635_;
goto v___jp_1840_;
}
v___jp_1659_:
{
lean_object* v___x_1673_; 
lean_inc_ref(v___y_1670_);
v___x_1673_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_1662_, v___y_1660_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1663_);
if (lean_obj_tag(v___x_1675_) == 0)
{
uint8_t v___x_1676_; 
lean_dec_ref(v___x_1675_);
v___x_1676_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_1674_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec_ref(v___y_1665_);
v___x_1677_ = lean_mk_empty_array_with_capacity(v___y_1671_);
lean_dec(v___y_1671_);
lean_inc_ref(v___x_1677_);
v___x_1678_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_1661_, v___x_1677_);
v___x_1679_ = l_Lean_Compiler_LCNF_inferAppType(v___y_1669_, v_fType_1653_, v___x_1678_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_n(v_a_1680_, 2);
lean_dec_ref(v___x_1679_);
v___x_1681_ = l_Lean_Expr_headBeta(v_a_1680_);
v___x_1682_ = l_Lean_Expr_isForall(v___x_1681_);
lean_dec_ref(v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v___x_1677_);
v___x_1683_ = l_Lean_Compiler_LCNF_mkAuxParam(v___y_1669_, v_a_1680_, v___x_1658_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_fvarId_1685_; lean_object* v___x_1686_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v_fvarId_1685_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1666_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1663_);
lean_inc(v_fvarId_1685_);
v___x_1686_ = lean_apply_9(v___y_1664_, v_fvarId_1685_, v___y_1660_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_, lean_box(0));
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
v___x_1690_ = lean_array_push(v___x_1689_, v_a_1684_);
v___x_1691_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
v___x_1692_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___y_1669_, v___x_1690_, v_a_1687_, v___x_1691_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_n(v_a_1693_, 2);
lean_dec_ref(v___x_1692_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1694_, 0, v_a_1693_);
lean_closure_set(v___f_1694_, 1, v___x_1688_);
v___x_1695_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1669_, v_a_1674_, v___f_1694_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1707_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1707_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_a_1693_);
lean_ctor_set(v___x_1700_, 1, v_a_1696_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1700_);
v___x_1702_ = v___x_1649_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1702_);
v___x_1704_ = v___x_1698_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
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
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1693_);
lean_del_object(v___x_1649_);
v_a_1708_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1695_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1695_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1674_);
lean_del_object(v___x_1649_);
v_a_1716_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1692_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1692_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
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
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_a_1684_);
lean_dec(v_a_1674_);
lean_del_object(v___x_1649_);
v_a_1724_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1686_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1686_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1674_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1660_);
lean_del_object(v___x_1649_);
v_a_1732_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1683_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1683_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v_a_1680_);
v___x_1740_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
v___x_1741_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(v___x_1677_, v_a_1674_, v___x_1740_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_1742_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_fvarId_1745_; lean_object* v___x_1746_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v_fvarId_1745_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1666_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1660_);
lean_inc(v_fvarId_1745_);
v___x_1746_ = lean_apply_9(v___y_1664_, v_fvarId_1745_, v___y_1660_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_, lean_box(0));
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1744_);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_mk_empty_array_with_capacity(v___x_1749_);
v___x_1751_ = lean_array_push(v___x_1750_, v___x_1748_);
v___x_1752_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v___x_1751_, v_a_1747_, v___y_1660_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_a_1753_);
v___x_1758_ = v___x_1649_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
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
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_del_object(v___x_1649_);
v_a_1764_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1752_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1752_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_a_1744_);
lean_dec_ref(v___y_1660_);
lean_del_object(v___x_1649_);
v_a_1772_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1746_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1746_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
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
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1660_);
lean_del_object(v___x_1649_);
v_a_1780_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1743_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1743_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1660_);
lean_del_object(v___x_1649_);
v_a_1788_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1741_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1741_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v___x_1677_);
lean_dec(v_a_1674_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1660_);
lean_del_object(v___x_1649_);
v_a_1796_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1679_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1679_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v___x_1804_; 
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_fType_1653_);
v___x_1804_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___y_1669_, v_a_1674_, v___y_1665_, v___y_1666_, v___y_1672_, v___y_1670_, v___y_1668_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_a_1805_);
v___x_1810_ = v___x_1649_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
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
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_del_object(v___x_1649_);
v_a_1816_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1804_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1804_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1674_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_fType_1653_);
lean_del_object(v___x_1649_);
v_a_1824_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1675_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1675_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
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
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_fType_1653_);
lean_del_object(v___x_1649_);
v_a_1832_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1673_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1673_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
v___jp_1840_:
{
if (v___x_1658_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_inc_ref_n(v_args_1654_, 2);
lean_inc_ref(v_fType_1653_);
lean_inc_ref(v_value_1652_);
lean_inc_ref(v_params_1651_);
lean_dec(v_val_1647_);
v___x_1848_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1657_);
v___x_1849_ = l_Array_toSubarray___redArg(v_args_1654_, v___x_1848_, v___x_1657_);
lean_inc_ref(v___x_1849_);
v___x_1850_ = l_Subarray_copy___redArg(v___x_1849_);
v___x_1851_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1651_, v_value_1652_, v___x_1850_, v___x_1658_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec_ref(v_params_1651_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___f_1856_; uint8_t v___x_1857_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = 0;
v___x_1854_ = lean_box(v___x_1853_);
lean_inc_ref(v_k_1628_);
lean_inc(v_fvarId_1637_);
lean_inc(v___x_1657_);
v___f_1855_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(v___f_1855_, 0, v___x_1657_);
lean_closure_set(v___f_1855_, 1, v___x_1656_);
lean_closure_set(v___f_1855_, 2, v_fvarId_1637_);
lean_closure_set(v___f_1855_, 3, v_k_1628_);
lean_closure_set(v___f_1855_, 4, v_args_1654_);
lean_closure_set(v___f_1855_, 5, v___x_1854_);
lean_closure_set(v___f_1855_, 6, v___x_1848_);
lean_inc_ref(v___y_1843_);
lean_inc_ref(v___y_1841_);
lean_inc_ref(v___f_1855_);
lean_inc(v___y_1842_);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1856_, 0, v___y_1842_);
lean_closure_set(v___f_1856_, 1, v___f_1855_);
lean_closure_set(v___f_1856_, 2, v___y_1841_);
lean_closure_set(v___f_1856_, 3, v___y_1843_);
v___x_1857_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(v_k_1628_, v_fvarId_1637_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
if (v___x_1857_ == 0)
{
lean_dec(v___x_1657_);
v___y_1660_ = v___y_1841_;
v___y_1661_ = v___x_1849_;
v___y_1662_ = v_a_1852_;
v___y_1663_ = v___y_1842_;
v___y_1664_ = v___f_1855_;
v___y_1665_ = v___f_1856_;
v___y_1666_ = v___y_1844_;
v___y_1667_ = v___y_1843_;
v___y_1668_ = v___y_1847_;
v___y_1669_ = v___x_1853_;
v___y_1670_ = v___y_1846_;
v___y_1671_ = v___x_1848_;
v___y_1672_ = v___y_1845_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_nat_dec_eq(v___x_1656_, v___x_1657_);
lean_dec(v___x_1657_);
if (v___x_1858_ == 0)
{
v___y_1660_ = v___y_1841_;
v___y_1661_ = v___x_1849_;
v___y_1662_ = v_a_1852_;
v___y_1663_ = v___y_1842_;
v___y_1664_ = v___f_1855_;
v___y_1665_ = v___f_1856_;
v___y_1666_ = v___y_1844_;
v___y_1667_ = v___y_1843_;
v___y_1668_ = v___y_1847_;
v___y_1669_ = v___x_1853_;
v___y_1670_ = v___y_1846_;
v___y_1671_ = v___x_1848_;
v___y_1672_ = v___y_1845_;
goto v___jp_1659_;
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref(v___f_1856_);
lean_dec_ref(v___f_1855_);
lean_dec_ref(v___x_1849_);
lean_dec_ref(v_fType_1653_);
lean_del_object(v___x_1649_);
v___x_1859_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1842_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v___x_1859_);
lean_inc_ref(v___y_1846_);
v___x_1860_ = l_Lean_Compiler_LCNF_Simp_simp(v_a_1852_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec_ref(v___y_1841_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1852_);
lean_dec_ref(v___y_1841_);
v_a_1878_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1859_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1859_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v___x_1849_);
lean_dec_ref(v___y_1841_);
lean_dec(v___x_1657_);
lean_dec_ref(v_args_1654_);
lean_dec_ref(v_fType_1653_);
lean_del_object(v___x_1649_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1886_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1851_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1851_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v___x_1894_; 
lean_dec(v___x_1657_);
lean_del_object(v___x_1649_);
v___x_1894_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(v_val_1647_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v_fvarId_1896_; lean_object* v___x_1897_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
v_fvarId_1896_ = lean_ctor_get(v_a_1895_, 0);
lean_inc(v_fvarId_1896_);
v___x_1897_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_1637_, v_fvarId_1896_, v___y_1842_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v___x_1897_);
v___x_1898_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_1842_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec_ref(v___x_1898_);
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1895_);
lean_ctor_set(v___x_1899_, 1, v_k_1628_);
lean_inc_ref(v___y_1846_);
v___x_1900_ = l_Lean_Compiler_LCNF_Simp_simp(v___x_1899_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec_ref(v___y_1841_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1900_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1900_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_a_1895_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_k_1628_);
v_a_1918_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1898_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1898_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_a_1895_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_k_1628_);
v_a_1926_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1897_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1897_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v___y_1841_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1934_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1894_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1894_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_dec(v_a_1643_);
lean_del_object(v___x_1640_);
lean_dec(v_value_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v___x_1963_ = lean_box(0);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1963_);
v___x_1965_ = v___x_1645_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1640_);
lean_dec(v_value_1638_);
lean_dec(v_fvarId_1637_);
lean_dec_ref(v_k_1628_);
v_a_1968_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1642_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1642_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void){
_start:
{
uint8_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = 0;
v___x_1980_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* v_cases_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_typeName_1993_; lean_object* v_discr_1994_; lean_object* v___x_1995_; lean_object* v_subst_1996_; uint8_t v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v_typeName_1993_ = lean_ctor_get(v_cases_1981_, 0);
v_discr_1994_ = lean_ctor_get(v_cases_1981_, 2);
v___x_1995_ = lean_st_ref_get(v_a_1983_);
v_subst_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_subst_1996_);
lean_dec(v___x_1995_);
v___x_1997_ = 0;
v___x_1998_ = 0;
lean_inc(v_discr_1994_);
v___x_1999_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1996_, v_discr_1994_, v___x_1998_);
lean_dec_ref(v_subst_1996_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_fvarId_2000_; lean_object* v___x_2001_; 
v_fvarId_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_fvarId_2000_);
lean_dec_ref(v___x_1999_);
v___x_2001_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_2000_, v_a_1984_, v_a_1986_, v_a_1988_);
lean_dec(v_fvarId_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2231_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2231_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2231_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
if (lean_obj_tag(v_a_2002_) == 1)
{
lean_object* v_val_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2226_; 
v_val_2006_ = lean_ctor_get(v_a_2002_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2008_ = v_a_2002_;
v_isShared_2009_ = v_isSharedCheck_2226_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_val_2006_);
lean_dec(v_a_2002_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2226_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v_env_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_get(v_a_1988_);
v_env_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_ref(v_env_2011_);
lean_dec(v___x_2010_);
v___x_2012_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_2006_);
lean_inc(v___x_2012_);
v___x_2013_ = l_Lean_Environment_find_x3f(v_env_2011_, v___x_2012_, v___x_1998_);
if (lean_obj_tag(v___x_2013_) == 1)
{
lean_object* v_val_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2225_; 
v_val_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2225_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_val_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2225_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
if (lean_obj_tag(v_val_2014_) == 6)
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2224_; 
v_val_2018_ = lean_ctor_get(v_val_2014_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_val_2014_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2020_ = v_val_2014_;
v_isShared_2021_ = v_isSharedCheck_2224_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v_val_2014_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2224_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_induct_2022_; uint8_t v___x_2023_; 
v_induct_2022_ = lean_ctor_get(v_val_2018_, 1);
lean_inc(v_induct_2022_);
lean_dec_ref(v_val_2018_);
v___x_2023_ = lean_name_eq(v_typeName_1993_, v_induct_2022_);
lean_dec(v_induct_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_del_object(v___x_2020_);
lean_del_object(v___x_2016_);
lean_dec(v___x_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
lean_dec_ref(v_cases_1981_);
v___x_2024_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2024_);
v___x_2026_ = v___x_2004_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
else
{
lean_object* v___x_2028_; lean_object* v_fst_2029_; lean_object* v_snd_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2223_; 
lean_del_object(v___x_2004_);
v___x_2028_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(v___x_1997_, v_cases_1981_, v___x_2012_);
v_fst_2029_ = lean_ctor_get(v___x_2028_, 0);
v_snd_2030_ = lean_ctor_get(v___x_2028_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2032_ = v___x_2028_;
v_isShared_2033_ = v_isSharedCheck_2223_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_snd_2030_);
lean_inc(v_fst_2029_);
lean_dec(v___x_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2223_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 4);
lean_ctor_set(v___x_2020_, 0, v_snd_2030_);
v___x_2035_ = v___x_2020_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_snd_2030_);
v___x_2035_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1997_, v___x_2035_, v_a_1986_);
lean_dec_ref(v___x_2035_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2037_; 
lean_dec_ref(v___x_2036_);
v___x_2037_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_1983_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_dec_ref(v___x_2037_);
if (lean_obj_tag(v_fst_2029_) == 0)
{
if (lean_obj_tag(v_val_2006_) == 0)
{
lean_object* v_params_2038_; lean_object* v_code_2039_; lean_object* v_val_2040_; lean_object* v_args_2041_; lean_object* v_lower_2043_; lean_object* v_upper_2044_; lean_object* v_numParams_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_del_object(v___x_2032_);
lean_del_object(v___x_2008_);
v_params_2038_ = lean_ctor_get(v_fst_2029_, 1);
lean_inc_ref(v_params_2038_);
v_code_2039_ = lean_ctor_get(v_fst_2029_, 2);
lean_inc_ref(v_code_2039_);
lean_dec_ref(v_fst_2029_);
v_val_2040_ = lean_ctor_get(v_val_2006_, 0);
lean_inc_ref(v_val_2040_);
v_args_2041_ = lean_ctor_get(v_val_2006_, 1);
lean_inc_ref(v_args_2041_);
lean_dec_ref(v_val_2006_);
v_numParams_2087_ = lean_ctor_get(v_val_2040_, 3);
lean_inc(v_numParams_2087_);
lean_dec_ref(v_val_2040_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_array_get_size(v_args_2041_);
v___x_2090_ = lean_nat_dec_le(v_numParams_2087_, v___x_2088_);
if (v___x_2090_ == 0)
{
v_lower_2043_ = v_numParams_2087_;
v_upper_2044_ = v___x_2089_;
goto v___jp_2042_;
}
else
{
lean_dec(v_numParams_2087_);
v_lower_2043_ = v___x_2088_;
v_upper_2044_ = v___x_2089_;
goto v___jp_2042_;
}
v___jp_2042_:
{
lean_object* v___x_2045_; size_t v_sz_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2045_ = l_Array_toSubarray___redArg(v_args_2041_, v_lower_2043_, v_upper_2044_);
v_sz_2046_ = lean_array_size(v_params_2038_);
v___x_2047_ = ((size_t)0ULL);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_2038_, v_sz_2046_, v___x_2047_, v___x_2045_, v_a_1983_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v___x_2049_; 
lean_dec_ref(v___x_2048_);
lean_inc_ref(v_a_1987_);
v___x_2049_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2039_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1997_, v_params_2038_, v_a_1986_);
lean_dec_ref(v_params_2038_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2061_; 
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2062_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2050_);
v___x_2056_ = v___x_2016_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2050_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
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
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2050_);
lean_del_object(v___x_2016_);
v_a_2063_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2051_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2051_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_params_2038_);
lean_del_object(v___x_2016_);
v_a_2071_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2049_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2049_);
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
lean_dec_ref(v_code_2039_);
lean_dec_ref(v_params_2038_);
lean_del_object(v___x_2016_);
v_a_2079_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2048_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2048_);
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
else
{
lean_object* v_params_2091_; lean_object* v_code_2092_; lean_object* v_n_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2184_; 
v_params_2091_ = lean_ctor_get(v_fst_2029_, 1);
lean_inc_ref(v_params_2091_);
v_code_2092_ = lean_ctor_get(v_fst_2029_, 2);
lean_inc_ref(v_code_2092_);
lean_dec_ref(v_fst_2029_);
v_n_2093_ = lean_ctor_get(v_val_2006_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_val_2006_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2095_ = v_val_2006_;
v_isShared_2096_ = v_isSharedCheck_2184_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_n_2093_);
lean_dec(v_val_2006_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2184_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_zero_2097_; uint8_t v_isZero_2098_; 
v_zero_2097_ = lean_unsigned_to_nat(0u);
v_isZero_2098_ = lean_nat_dec_eq(v_n_2093_, v_zero_2097_);
if (v_isZero_2098_ == 1)
{
lean_object* v___x_2099_; 
lean_del_object(v___x_2095_);
lean_dec(v_n_2093_);
lean_dec_ref(v_params_2091_);
lean_del_object(v___x_2032_);
lean_del_object(v___x_2008_);
lean_inc_ref(v_a_1987_);
v___x_2099_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2092_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2110_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2100_);
v___x_2105_ = v___x_2016_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_del_object(v___x_2016_);
v_a_2111_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2099_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2099_);
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
lean_object* v_one_2119_; lean_object* v_n_2120_; lean_object* v___x_2122_; 
v_one_2119_ = lean_unsigned_to_nat(1u);
v_n_2120_ = lean_nat_sub(v_n_2093_, v_one_2119_);
lean_dec(v_n_2093_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 0);
lean_ctor_set(v___x_2095_, 0, v_n_2120_);
v___x_2122_ = v___x_2095_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_n_2120_);
v___x_2122_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2122_);
v___x_2124_ = v___x_2008_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
v___x_2126_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1997_, v___x_2124_, v___x_2125_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_fvarId_2130_; lean_object* v_fvarId_2131_; lean_object* v___x_2132_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
v___x_2129_ = lean_array_get_borrowed(v___x_2128_, v_params_2091_, v_zero_2097_);
v_fvarId_2130_ = lean_ctor_get(v___x_2129_, 0);
v_fvarId_2131_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_fvarId_2131_);
lean_inc(v_fvarId_2130_);
v___x_2132_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2130_, v_fvarId_2131_, v_a_1983_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref(v___x_2132_);
lean_inc_ref(v_a_1987_);
v___x_2133_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2092_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1997_, v_params_2091_, v_a_1986_);
lean_dec_ref(v_params_2091_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2148_; 
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v___x_2135_, 0);
lean_dec(v_unused_2149_);
v___x_2137_ = v___x_2135_;
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v___x_2135_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2134_);
lean_ctor_set(v___x_2032_, 0, v_a_2127_);
v___x_2140_ = v___x_2032_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2127_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_a_2134_);
v___x_2140_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2140_);
v___x_2142_ = v___x_2016_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2142_);
v___x_2144_ = v___x_2137_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
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
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2134_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2032_);
lean_del_object(v___x_2016_);
v_a_2150_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2135_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2135_);
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
lean_dec(v_a_2127_);
lean_dec_ref(v_params_2091_);
lean_del_object(v___x_2032_);
lean_del_object(v___x_2016_);
v_a_2158_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2133_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2133_);
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
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2127_);
lean_dec_ref(v_code_2092_);
lean_dec_ref(v_params_2091_);
lean_del_object(v___x_2032_);
lean_del_object(v___x_2016_);
v_a_2166_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2132_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2132_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_code_2092_);
lean_dec_ref(v_params_2091_);
lean_del_object(v___x_2032_);
lean_del_object(v___x_2016_);
v_a_2174_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2126_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2126_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
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
lean_object* v_code_2185_; lean_object* v___x_2186_; 
lean_del_object(v___x_2032_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
v_code_2185_ = lean_ctor_get(v_fst_2029_, 0);
lean_inc_ref(v_code_2185_);
lean_dec_ref(v_fst_2029_);
lean_inc_ref(v_a_1987_);
v___x_2186_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2185_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2197_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2187_);
v___x_2192_ = v___x_2016_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2016_);
v_a_2198_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2186_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2186_);
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
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2032_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2016_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
v_a_2206_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2037_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2037_);
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
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_del_object(v___x_2032_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2016_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
v_a_2214_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2036_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2036_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
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
lean_del_object(v___x_2016_);
lean_dec(v_val_2014_);
lean_dec(v___x_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_cases_1981_);
goto v___jp_1990_;
}
}
}
else
{
lean_dec(v___x_2013_);
lean_dec(v___x_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_val_2006_);
lean_del_object(v___x_2004_);
lean_dec_ref(v_cases_1981_);
goto v___jp_1990_;
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_dec(v_a_2002_);
lean_dec_ref(v_cases_1981_);
v___x_2227_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2227_);
v___x_2229_ = v___x_2004_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
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
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_cases_1981_);
v_a_2232_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2001_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2001_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2240_; 
lean_dec_ref(v_cases_1981_);
v___x_2240_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_1997_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2240_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2240_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
v___jp_1990_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* v_fvarId_2258_, lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v_i_2261_, lean_object* v_as_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_array_get_size(v_as_2262_);
v___x_2272_ = lean_nat_dec_lt(v_i_2261_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_as_2262_);
return v___x_2273_;
}
else
{
lean_object* v_a_2274_; lean_object* v_a_2276_; 
v_a_2274_ = lean_array_fget_borrowed(v_as_2262_, v_i_2261_);
if (lean_obj_tag(v_a_2274_) == 0)
{
lean_object* v_ctorName_2287_; lean_object* v_params_2288_; lean_object* v_code_2289_; uint8_t v___x_2290_; uint8_t v___y_2292_; uint8_t v___x_2344_; uint8_t v___y_2346_; uint8_t v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_ctorName_2287_ = lean_ctor_get(v_a_2274_, 0);
v_params_2288_ = lean_ctor_get(v_a_2274_, 1);
v_code_2289_ = lean_ctor_get(v_a_2274_, 2);
v___x_2290_ = 0;
v___x_2344_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_array_get_size(v_params_2288_);
v___x_2351_ = lean_nat_dec_lt(v___x_2349_, v___x_2350_);
if (v___x_2351_ == 0)
{
v_a_2348_ = v___x_2344_;
goto v___jp_2347_;
}
else
{
if (v___x_2351_ == 0)
{
v_a_2348_ = v___x_2344_;
goto v___jp_2347_;
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2350_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_2288_, v___x_2352_, v___x_2353_, v___y_2269_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_unbox(v_a_2355_);
lean_dec(v_a_2355_);
v_a_2348_ = v___x_2356_;
goto v___jp_2347_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
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
}
v___jp_2291_:
{
if (v___y_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_inc_ref(v_params_2288_);
lean_inc(v_ctorName_2287_);
lean_inc(v_fvarId_2258_);
v___x_2293_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_2258_, v_ctorName_2287_, v_params_2288_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
lean_inc_ref(v___y_2268_);
lean_inc_ref(v_code_2289_);
v___x_2295_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2289_, v___y_2263_, v___y_2264_, v_a_2294_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v_a_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
lean_inc_ref(v_a_2274_);
v___x_2297_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2274_, v_a_2296_);
v_a_2276_ = v___x_2297_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
v_a_2298_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2295_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2295_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
v_a_2306_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2293_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2293_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v___x_2314_; 
lean_inc_ref(v_code_2289_);
v___x_2314_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_2290_, v_code_2289_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_2290_, v_code_2289_, v___y_2267_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref(v___x_2316_);
v___x_2317_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2264_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref(v___x_2317_);
v___x_2318_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2315_);
lean_inc_ref(v_a_2274_);
v___x_2319_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2274_, v___x_2318_);
v_a_2276_ = v___x_2319_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2315_);
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
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
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
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
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
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
v___jp_2345_:
{
if (v___x_2344_ == 0)
{
v___y_2292_ = v___x_2344_;
goto v___jp_2291_;
}
else
{
v___y_2292_ = v___y_2346_;
goto v___jp_2291_;
}
}
v___jp_2347_:
{
if (lean_obj_tag(v_code_2289_) == 6)
{
v___y_2346_ = v_a_2348_;
goto v___jp_2345_;
}
else
{
if (v___x_2344_ == 0)
{
v___y_2292_ = v_a_2348_;
goto v___jp_2291_;
}
else
{
v___y_2346_ = v_a_2348_;
goto v___jp_2345_;
}
}
}
}
else
{
lean_object* v_code_2365_; lean_object* v___x_2366_; 
v_code_2365_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v___y_2268_);
lean_inc_ref(v_code_2365_);
v___x_2366_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_2365_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref(v___x_2366_);
lean_inc_ref(v_a_2274_);
v___x_2368_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2274_, v_a_2367_);
v_a_2276_ = v___x_2368_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_as_2262_);
lean_dec(v_i_2261_);
lean_dec(v_fvarId_2258_);
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
v___jp_2275_:
{
size_t v___x_2277_; size_t v___x_2278_; uint8_t v___x_2279_; 
v___x_2277_ = lean_ptr_addr(v_a_2274_);
v___x_2278_ = lean_ptr_addr(v_a_2276_);
v___x_2279_ = lean_usize_dec_eq(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_nat_add(v_i_2261_, v___x_2280_);
v___x_2282_ = lean_array_fset(v_as_2262_, v_i_2261_, v_a_2276_);
lean_dec(v_i_2261_);
v_i_2261_ = v___x_2281_;
v_as_2262_ = v___x_2282_;
goto _start;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_a_2276_);
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_i_2261_, v___x_2284_);
lean_dec(v_i_2261_);
v_i_2261_ = v___x_2285_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* v_code_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___y_2387_; lean_object* v___y_2388_; uint8_t v___y_2389_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; lean_object* v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2423_; lean_object* v___y_2424_; lean_object* v_decl_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; uint8_t v___y_2474_; lean_object* v___y_2475_; lean_object* v_decl_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v_fileName_2501_; lean_object* v_fileMap_2502_; lean_object* v_options_2503_; lean_object* v_currRecDepth_2504_; lean_object* v_maxRecDepth_2505_; lean_object* v_ref_2506_; lean_object* v_currNamespace_2507_; lean_object* v_openDecls_2508_; lean_object* v_initHeartbeats_2509_; lean_object* v_maxHeartbeats_2510_; lean_object* v_quotContext_2511_; lean_object* v_currMacroScope_2512_; uint8_t v_diag_2513_; lean_object* v_cancelTk_x3f_2514_; uint8_t v_suppressElabErrors_2515_; lean_object* v_inheritedTraceOptions_2516_; uint8_t v___x_2517_; 
v_fileName_2501_ = lean_ctor_get(v_a_2383_, 0);
v_fileMap_2502_ = lean_ctor_get(v_a_2383_, 1);
v_options_2503_ = lean_ctor_get(v_a_2383_, 2);
v_currRecDepth_2504_ = lean_ctor_get(v_a_2383_, 3);
v_maxRecDepth_2505_ = lean_ctor_get(v_a_2383_, 4);
v_ref_2506_ = lean_ctor_get(v_a_2383_, 5);
v_currNamespace_2507_ = lean_ctor_get(v_a_2383_, 6);
v_openDecls_2508_ = lean_ctor_get(v_a_2383_, 7);
v_initHeartbeats_2509_ = lean_ctor_get(v_a_2383_, 8);
v_maxHeartbeats_2510_ = lean_ctor_get(v_a_2383_, 9);
v_quotContext_2511_ = lean_ctor_get(v_a_2383_, 10);
v_currMacroScope_2512_ = lean_ctor_get(v_a_2383_, 11);
v_diag_2513_ = lean_ctor_get_uint8(v_a_2383_, sizeof(void*)*14);
v_cancelTk_x3f_2514_ = lean_ctor_get(v_a_2383_, 12);
v_suppressElabErrors_2515_ = lean_ctor_get_uint8(v_a_2383_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2516_ = lean_ctor_get(v_a_2383_, 13);
v___x_2517_ = lean_nat_dec_eq(v_currRecDepth_2504_, v_maxRecDepth_2505_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_inc_ref(v_inheritedTraceOptions_2516_);
lean_inc(v_cancelTk_x3f_2514_);
lean_inc(v_currMacroScope_2512_);
lean_inc(v_quotContext_2511_);
lean_inc(v_maxHeartbeats_2510_);
lean_inc(v_initHeartbeats_2509_);
lean_inc(v_openDecls_2508_);
lean_inc(v_currNamespace_2507_);
lean_inc(v_ref_2506_);
lean_inc(v_maxRecDepth_2505_);
lean_inc(v_currRecDepth_2504_);
lean_inc_ref(v_options_2503_);
lean_inc_ref(v_fileMap_2502_);
lean_inc_ref(v_fileName_2501_);
lean_dec_ref(v_a_2383_);
v___x_2518_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2379_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_3270_; 
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_3270_ == 0)
{
lean_object* v_unused_3271_; 
v_unused_3271_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_3271_);
v___x_2520_ = v___x_2518_;
v_isShared_2521_ = v_isSharedCheck_3270_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2518_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_3270_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_decl_2523_; lean_object* v_k_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_add(v_currRecDepth_2504_, v___x_2596_);
lean_inc(v_maxRecDepth_2505_);
v___x_2598_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2598_, 0, v_fileName_2501_);
lean_ctor_set(v___x_2598_, 1, v_fileMap_2502_);
lean_ctor_set(v___x_2598_, 2, v_options_2503_);
lean_ctor_set(v___x_2598_, 3, v___x_2597_);
lean_ctor_set(v___x_2598_, 4, v_maxRecDepth_2505_);
lean_ctor_set(v___x_2598_, 5, v_ref_2506_);
lean_ctor_set(v___x_2598_, 6, v_currNamespace_2507_);
lean_ctor_set(v___x_2598_, 7, v_openDecls_2508_);
lean_ctor_set(v___x_2598_, 8, v_initHeartbeats_2509_);
lean_ctor_set(v___x_2598_, 9, v_maxHeartbeats_2510_);
lean_ctor_set(v___x_2598_, 10, v_quotContext_2511_);
lean_ctor_set(v___x_2598_, 11, v_currMacroScope_2512_);
lean_ctor_set(v___x_2598_, 12, v_cancelTk_x3f_2514_);
lean_ctor_set(v___x_2598_, 13, v_inheritedTraceOptions_2516_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*14, v_diag_2513_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*14 + 1, v_suppressElabErrors_2515_);
switch(lean_obj_tag(v_code_2377_))
{
case 0:
{
lean_object* v_decl_2599_; lean_object* v_k_2600_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; uint8_t v___y_2610_; uint8_t v___x_2824_; lean_object* v_decl_2826_; lean_object* v_type_2827_; lean_object* v_value_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___x_2839_; 
lean_del_object(v___x_2520_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_decl_2599_ = lean_ctor_get(v_code_2377_, 0);
v_k_2600_ = lean_ctor_get(v_code_2377_, 1);
v___x_2824_ = 0;
lean_inc_ref(v_decl_2599_);
v___x_2839_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_2824_, v___x_2517_, v_decl_2599_, v_a_2379_, v_a_2382_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; uint8_t v___x_2893_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2839_);
v___x_2893_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(v___x_2824_, v_decl_2599_, v_a_2840_);
if (v___x_2893_ == 0)
{
goto v___jp_2883_;
}
else
{
if (v___x_2517_ == 0)
{
v___y_2842_ = v_a_2378_;
v___y_2843_ = v_a_2379_;
v___y_2844_ = v_a_2380_;
v___y_2845_ = v_a_2381_;
v___y_2846_ = v_a_2382_;
v___y_2847_ = v___x_2598_;
v___y_2848_ = v_a_2384_;
goto v___jp_2841_;
}
else
{
goto v___jp_2883_;
}
}
v___jp_2841_:
{
lean_object* v_type_2849_; lean_object* v_value_2850_; lean_object* v___x_2851_; 
v_type_2849_ = lean_ctor_get(v_a_2840_, 2);
v_value_2850_ = lean_ctor_get(v_a_2840_, 3);
lean_inc(v_value_2850_);
v___x_2851_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(v_value_2850_, v___y_2842_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v_a_2852_) == 1)
{
lean_object* v_val_2853_; lean_object* v___x_2854_; 
v_val_2853_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_val_2853_);
lean_dec_ref(v_a_2852_);
v___x_2854_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2843_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v___x_2854_);
v___x_2855_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_2824_, v_a_2840_, v_val_2853_, v___y_2846_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v_type_2857_; lean_object* v_value_2858_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v_type_2857_ = lean_ctor_get(v_a_2856_, 2);
lean_inc_ref(v_type_2857_);
v_value_2858_ = lean_ctor_get(v_a_2856_, 3);
lean_inc(v_value_2858_);
v_decl_2826_ = v_a_2856_;
v_type_2827_ = v_type_2857_;
v_value_2828_ = v_value_2858_;
v___y_2829_ = v___y_2842_;
v___y_2830_ = v___y_2843_;
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2845_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
goto v___jp_2825_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_code_2377_);
v_a_2859_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2855_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2855_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_val_2853_);
lean_dec_ref(v___y_2847_);
lean_dec(v_a_2840_);
lean_dec_ref(v_code_2377_);
v_a_2867_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2854_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2854_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_inc(v_value_2850_);
lean_inc_ref(v_type_2849_);
lean_dec(v_a_2852_);
v_decl_2826_ = v_a_2840_;
v_type_2827_ = v_type_2849_;
v_value_2828_ = v_value_2850_;
v___y_2829_ = v___y_2842_;
v___y_2830_ = v___y_2843_;
v___y_2831_ = v___y_2844_;
v___y_2832_ = v___y_2845_;
v___y_2833_ = v___y_2846_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v___y_2847_);
lean_dec(v_a_2840_);
lean_dec_ref(v_code_2377_);
v_a_2875_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2851_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2851_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
v___jp_2883_:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2379_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref(v___x_2884_);
v___y_2842_ = v_a_2378_;
v___y_2843_ = v_a_2379_;
v___y_2844_ = v_a_2380_;
v___y_2845_ = v_a_2381_;
v___y_2846_ = v_a_2382_;
v___y_2847_ = v___x_2598_;
v___y_2848_ = v_a_2384_;
goto v___jp_2841_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_a_2840_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
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
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
v_a_2894_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2839_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2839_);
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
v___jp_2601_:
{
if (v___y_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_inc_ref(v___y_2607_);
v___x_2611_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(v___y_2607_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref(v___x_2611_);
if (lean_obj_tag(v_a_2612_) == 1)
{
lean_object* v_val_2613_; lean_object* v___x_2614_; 
lean_inc_ref(v_k_2600_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_code_2377_);
v_val_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_val_2613_);
lean_dec_ref(v_a_2612_);
v___x_2614_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2609_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2615_; 
lean_dec_ref(v___x_2614_);
lean_inc_ref(v___y_2603_);
v___x_2615_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2600_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_val_2613_, v_a_2616_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
lean_dec_ref(v___y_2603_);
lean_dec(v_val_2613_);
return v___x_2617_;
}
else
{
lean_dec(v_val_2613_);
lean_dec_ref(v___y_2603_);
return v___x_2615_;
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_val_2613_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2618_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2614_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2614_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_a_2612_);
lean_inc_ref(v___y_2607_);
v___x_2626_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(v___y_2607_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
if (lean_obj_tag(v_a_2627_) == 1)
{
lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2636_; 
lean_inc_ref(v_k_2600_);
lean_dec_ref(v___y_2607_);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_code_2377_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; lean_object* v_unused_2638_; 
v_unused_2637_ = lean_ctor_get(v_code_2377_, 1);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_code_2377_, 0);
lean_dec(v_unused_2638_);
v___x_2629_ = v_code_2377_;
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v_code_2377_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_val_2631_; lean_object* v___x_2633_; 
v_val_2631_ = lean_ctor_get(v_a_2627_, 0);
lean_inc(v_val_2631_);
lean_dec_ref(v_a_2627_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 1);
lean_ctor_set(v___x_2629_, 0, v_val_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_val_2631_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_k_2600_);
v___x_2633_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
v_code_2377_ = v___x_2633_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2609_;
v_a_2380_ = v___y_2605_;
v_a_2381_ = v___y_2608_;
v_a_2382_ = v___y_2604_;
v_a_2383_ = v___y_2603_;
v_a_2384_ = v___y_2602_;
goto _start;
}
}
}
else
{
lean_object* v_fvarId_2639_; lean_object* v_value_2640_; lean_object* v___x_2641_; 
lean_dec(v_a_2627_);
v_fvarId_2639_ = lean_ctor_get(v___y_2607_, 0);
v_value_2640_ = lean_ctor_get(v___y_2607_, 3);
v___x_2641_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_2640_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2641_);
if (lean_obj_tag(v_a_2642_) == 1)
{
lean_object* v_val_2643_; lean_object* v___x_2644_; 
lean_inc_ref(v_k_2600_);
lean_dec_ref(v_code_2377_);
v_val_2643_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_val_2643_);
lean_dec_ref(v_a_2642_);
lean_inc(v_fvarId_2639_);
v___x_2644_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2639_, v_val_2643_, v___y_2609_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; 
lean_dec_ref(v___x_2644_);
v___x_2645_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2607_, v___y_2609_, v___y_2604_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_dec_ref(v___x_2645_);
v_code_2377_ = v_k_2600_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2609_;
v_a_2380_ = v___y_2605_;
v_a_2381_ = v___y_2608_;
v_a_2382_ = v___y_2604_;
v_a_2383_ = v___y_2603_;
v_a_2384_ = v___y_2602_;
goto _start;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2647_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2645_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2655_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2644_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2644_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_a_2642_);
lean_inc_ref(v_k_2600_);
lean_inc_ref(v___y_2607_);
v___x_2663_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v___y_2607_, v_k_2600_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
if (lean_obj_tag(v_a_2664_) == 1)
{
lean_object* v_val_2665_; lean_object* v___x_2666_; 
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_val_2665_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_val_2665_);
lean_dec_ref(v_a_2664_);
v___x_2666_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2607_, v___y_2609_, v___y_2604_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2674_);
v___x_2668_ = v___x_2666_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2666_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v_val_2665_);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_val_2665_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_val_2665_);
v_a_2675_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2666_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2666_);
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
lean_dec(v_a_2664_);
lean_inc(v_value_2640_);
v___x_2683_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_value_2640_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
if (lean_obj_tag(v_a_2684_) == 1)
{
lean_object* v_val_2685_; lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___x_2688_; 
lean_inc_ref(v_k_2600_);
lean_dec_ref(v_code_2377_);
v_val_2685_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_val_2685_);
lean_dec_ref(v_a_2684_);
v_fst_2686_ = lean_ctor_get(v_val_2685_, 0);
lean_inc(v_fst_2686_);
v_snd_2687_ = lean_ctor_get(v_val_2685_, 1);
lean_inc(v_snd_2687_);
lean_dec(v_val_2685_);
lean_inc(v_fvarId_2639_);
v___x_2688_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2639_, v_snd_2687_, v___y_2609_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2689_; 
lean_dec_ref(v___x_2688_);
v___x_2689_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2607_, v___y_2609_, v___y_2604_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2690_; 
lean_dec_ref(v___x_2689_);
lean_inc_ref(v___y_2603_);
v___x_2690_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2600_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_2686_, v_a_2691_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
lean_dec_ref(v___y_2603_);
lean_dec(v_fst_2686_);
return v___x_2692_;
}
else
{
lean_dec(v_fst_2686_);
lean_dec_ref(v___y_2603_);
return v___x_2690_;
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_fst_2686_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2693_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2689_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2689_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_fst_2686_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2701_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2688_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2688_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_a_2684_);
lean_inc_ref(v___y_2603_);
lean_inc_ref(v_k_2600_);
v___x_2709_ = l_Lean_Compiler_LCNF_Simp_simp(v_k_2600_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2639_, v___y_2609_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = lean_unbox(v_a_2712_);
lean_dec(v_a_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v___x_2714_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2607_, v___y_2609_, v___y_2604_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; 
v_unused_2722_ = lean_ctor_get(v___x_2714_, 0);
lean_dec(v_unused_2722_);
v___x_2716_ = v___x_2714_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_dec(v___x_2714_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v_a_2710_);
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2710_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_a_2710_);
v_a_2723_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2714_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2714_);
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
else
{
lean_object* v___x_2731_; 
lean_inc_ref(v___y_2607_);
v___x_2731_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_2607_, v___y_2606_, v___y_2609_, v___y_2605_, v___y_2608_, v___y_2604_, v___y_2603_, v___y_2602_);
lean_dec_ref(v___y_2603_);
if (lean_obj_tag(v___x_2731_) == 0)
{
size_t v___x_2732_; size_t v___x_2733_; uint8_t v___x_2734_; 
lean_dec_ref(v___x_2731_);
v___x_2732_ = lean_ptr_addr(v_k_2600_);
v___x_2733_ = lean_ptr_addr(v_a_2710_);
v___x_2734_ = lean_usize_dec_eq(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
v___y_2495_ = v___y_2607_;
v___y_2496_ = v_a_2710_;
v___y_2497_ = v___x_2734_;
goto v___jp_2494_;
}
else
{
size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_ptr_addr(v_decl_2599_);
v___x_2736_ = lean_ptr_addr(v___y_2607_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
v___y_2495_ = v___y_2607_;
v___y_2496_ = v_a_2710_;
v___y_2497_ = v___x_2737_;
goto v___jp_2494_;
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_code_2377_);
v_a_2738_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2731_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2731_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2746_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2711_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2711_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
return v___x_2709_;
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2754_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2683_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2683_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2762_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2663_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2663_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2770_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2641_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2641_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2778_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2626_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2626_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_code_2377_);
v_a_2786_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2611_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2611_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v_fvarId_2795_; lean_object* v_subst_2796_; lean_object* v_used_2797_; lean_object* v_binderRenaming_2798_; lean_object* v_funDeclInfoMap_2799_; uint8_t v_simplified_2800_; lean_object* v_visited_2801_; lean_object* v_inline_2802_; lean_object* v_inlineLocal_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2823_; 
lean_inc_ref(v_k_2600_);
lean_dec_ref(v_code_2377_);
v___x_2794_ = lean_st_ref_take(v___y_2609_);
v_fvarId_2795_ = lean_ctor_get(v___y_2607_, 0);
v_subst_2796_ = lean_ctor_get(v___x_2794_, 0);
v_used_2797_ = lean_ctor_get(v___x_2794_, 1);
v_binderRenaming_2798_ = lean_ctor_get(v___x_2794_, 2);
v_funDeclInfoMap_2799_ = lean_ctor_get(v___x_2794_, 3);
v_simplified_2800_ = lean_ctor_get_uint8(v___x_2794_, sizeof(void*)*7);
v_visited_2801_ = lean_ctor_get(v___x_2794_, 4);
v_inline_2802_ = lean_ctor_get(v___x_2794_, 5);
v_inlineLocal_2803_ = lean_ctor_get(v___x_2794_, 6);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2805_ = v___x_2794_;
v_isShared_2806_ = v_isSharedCheck_2823_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_inlineLocal_2803_);
lean_inc(v_inline_2802_);
lean_inc(v_visited_2801_);
lean_inc(v_funDeclInfoMap_2799_);
lean_inc(v_binderRenaming_2798_);
lean_inc(v_used_2797_);
lean_inc(v_subst_2796_);
lean_dec(v___x_2794_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2823_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2807_ = lean_box(0);
lean_inc(v_fvarId_2795_);
v___x_2808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_2796_, v_fvarId_2795_, v___x_2807_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2808_);
v___x_2810_ = v___x_2805_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_used_2797_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_binderRenaming_2798_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_funDeclInfoMap_2799_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_visited_2801_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_inline_2802_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_inlineLocal_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*7, v_simplified_2800_);
v___x_2810_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_st_ref_set(v___y_2609_, v___x_2810_);
v___x_2812_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_2607_, v___y_2609_, v___y_2604_);
lean_dec_ref(v___y_2607_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_dec_ref(v___x_2812_);
v_code_2377_ = v_k_2600_;
v_a_2378_ = v___y_2606_;
v_a_2379_ = v___y_2609_;
v_a_2380_ = v___y_2605_;
v_a_2381_ = v___y_2608_;
v_a_2382_ = v___y_2604_;
v_a_2383_ = v___y_2603_;
v_a_2384_ = v___y_2602_;
goto _start;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_k_2600_);
v_a_2814_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2812_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2812_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
}
v___jp_2825_:
{
uint8_t v___x_2836_; 
v___x_2836_ = l_Lean_Expr_isErased(v_type_2827_);
lean_dec_ref(v_type_2827_);
if (v___x_2836_ == 0)
{
lean_dec(v_value_2828_);
v___y_2602_ = v___y_2835_;
v___y_2603_ = v___y_2834_;
v___y_2604_ = v___y_2833_;
v___y_2605_ = v___y_2831_;
v___y_2606_ = v___y_2829_;
v___y_2607_ = v_decl_2826_;
v___y_2608_ = v___y_2832_;
v___y_2609_ = v___y_2830_;
v___y_2610_ = v___x_2517_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = lean_box(1);
v___x_2838_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(v___x_2824_, v_value_2828_, v___x_2837_);
lean_dec(v_value_2828_);
if (v___x_2838_ == 0)
{
v___y_2602_ = v___y_2835_;
v___y_2603_ = v___y_2834_;
v___y_2604_ = v___y_2833_;
v___y_2605_ = v___y_2831_;
v___y_2606_ = v___y_2829_;
v___y_2607_ = v_decl_2826_;
v___y_2608_ = v___y_2832_;
v___y_2609_ = v___y_2830_;
v___y_2610_ = v___x_2836_;
goto v___jp_2601_;
}
else
{
v___y_2602_ = v___y_2835_;
v___y_2603_ = v___y_2834_;
v___y_2604_ = v___y_2833_;
v___y_2605_ = v___y_2831_;
v___y_2606_ = v___y_2829_;
v___y_2607_ = v_decl_2826_;
v___y_2608_ = v___y_2832_;
v___y_2609_ = v___y_2830_;
v___y_2610_ = v___x_2517_;
goto v___jp_2601_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_2902_; lean_object* v_args_2903_; lean_object* v___x_2904_; lean_object* v_subst_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; 
lean_del_object(v___x_2520_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_fvarId_2902_ = lean_ctor_get(v_code_2377_, 0);
v_args_2903_ = lean_ctor_get(v_code_2377_, 1);
v___x_2904_ = lean_st_ref_get(v_a_2379_);
v_subst_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc_ref(v_subst_2905_);
lean_dec(v___x_2904_);
v___x_2906_ = 0;
lean_inc(v_fvarId_2902_);
v___x_2907_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2905_, v_fvarId_2902_, v___x_2517_);
lean_dec_ref(v_subst_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_fvarId_2908_; lean_object* v___x_2909_; 
v_fvarId_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_fvarId_2908_);
lean_dec_ref(v___x_2907_);
lean_inc_ref(v_args_2903_);
v___x_2909_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_2906_, v___x_2517_, v_args_2903_, v_a_2379_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2978_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2978_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2978_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
uint8_t v___y_2915_; lean_object* v___y_2937_; lean_object* v___x_2946_; 
lean_inc(v_a_2910_);
v___x_2946_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(v_fvarId_2908_, v_a_2910_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
if (lean_obj_tag(v_a_2947_) == 1)
{
lean_object* v_val_2948_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_dec(v_fvarId_2908_);
lean_dec_ref(v_code_2377_);
v_val_2948_ = lean_ctor_get(v_a_2947_, 0);
lean_inc(v_val_2948_);
lean_dec_ref(v_a_2947_);
v_code_2377_ = v_val_2948_;
v_a_2383_ = v___x_2598_;
goto _start;
}
else
{
lean_object* v___x_2950_; 
lean_dec(v_a_2947_);
lean_dec_ref(v___x_2598_);
lean_inc(v_fvarId_2908_);
v___x_2950_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_2908_, v_a_2379_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
lean_dec_ref(v___x_2950_);
v___x_2951_ = lean_unsigned_to_nat(0u);
v___x_2952_ = lean_array_get_size(v_a_2910_);
v___x_2953_ = lean_nat_dec_lt(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
goto v___jp_2931_;
}
else
{
lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_nat_dec_le(v___x_2952_, v___x_2952_);
if (v___x_2955_ == 0)
{
if (v___x_2953_ == 0)
{
goto v___jp_2931_;
}
else
{
size_t v___x_2956_; size_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = lean_usize_of_nat(v___x_2952_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_2910_, v___x_2956_, v___x_2957_, v___x_2954_, v_a_2379_);
v___y_2937_ = v___x_2958_;
goto v___jp_2936_;
}
}
else
{
size_t v___x_2959_; size_t v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = ((size_t)0ULL);
v___x_2960_ = lean_usize_of_nat(v___x_2952_);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_2910_, v___x_2959_, v___x_2960_, v___x_2954_, v_a_2379_);
v___y_2937_ = v___x_2961_;
goto v___jp_2936_;
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_dec(v_fvarId_2908_);
lean_dec_ref(v_code_2377_);
v_a_2962_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2950_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2950_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_dec(v_fvarId_2908_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
v_a_2970_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2946_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2946_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
v___jp_2914_:
{
if (v___y_2915_ == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2925_; 
v_isSharedCheck_2925_ = !lean_is_exclusive(v_code_2377_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; lean_object* v_unused_2927_; 
v_unused_2926_ = lean_ctor_get(v_code_2377_, 1);
lean_dec(v_unused_2926_);
v_unused_2927_ = lean_ctor_get(v_code_2377_, 0);
lean_dec(v_unused_2927_);
v___x_2917_ = v_code_2377_;
v_isShared_2918_ = v_isSharedCheck_2925_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v_code_2377_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2925_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v_a_2910_);
lean_ctor_set(v___x_2917_, 0, v_fvarId_2908_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_fvarId_2908_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_a_2910_);
v___x_2920_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2920_);
v___x_2922_ = v___x_2912_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
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
else
{
lean_object* v___x_2929_; 
lean_dec(v_a_2910_);
lean_dec(v_fvarId_2908_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_code_2377_);
v___x_2929_ = v___x_2912_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_code_2377_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
v___jp_2931_:
{
uint8_t v___x_2932_; 
v___x_2932_ = l_Lean_instBEqFVarId_beq(v_fvarId_2902_, v_fvarId_2908_);
if (v___x_2932_ == 0)
{
v___y_2915_ = v___x_2932_;
goto v___jp_2914_;
}
else
{
size_t v___x_2933_; size_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2933_ = lean_ptr_addr(v_args_2903_);
v___x_2934_ = lean_ptr_addr(v_a_2910_);
v___x_2935_ = lean_usize_dec_eq(v___x_2933_, v___x_2934_);
v___y_2915_ = v___x_2935_;
goto v___jp_2914_;
}
}
v___jp_2936_:
{
if (lean_obj_tag(v___y_2937_) == 0)
{
lean_dec_ref(v___y_2937_);
goto v___jp_2931_;
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_dec(v_fvarId_2908_);
lean_dec_ref(v_code_2377_);
v_a_2938_ = lean_ctor_get(v___y_2937_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___y_2937_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___y_2937_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___y_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_fvarId_2908_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
v_a_2979_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2909_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2909_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v___x_2987_; 
lean_dec_ref(v_code_2377_);
v___x_2987_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2906_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
lean_dec_ref(v___x_2598_);
return v___x_2987_;
}
}
case 4:
{
lean_object* v_cases_2988_; lean_object* v___x_2989_; 
lean_del_object(v___x_2520_);
v_cases_2988_ = lean_ctor_get(v_code_2377_, 0);
lean_inc_ref_n(v_cases_2988_, 2);
v___x_2989_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_2988_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3201_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3201_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3201_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
if (lean_obj_tag(v_a_2990_) == 1)
{
lean_object* v_val_2994_; lean_object* v___x_2996_; 
lean_dec_ref(v_code_2377_);
lean_dec_ref(v_cases_2988_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_val_2994_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_val_2994_);
lean_dec_ref(v_a_2990_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_val_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_val_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
else
{
lean_object* v_typeName_2998_; lean_object* v_resultType_2999_; lean_object* v_discr_3000_; lean_object* v_alts_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_2990_);
v_typeName_2998_ = lean_ctor_get(v_cases_2988_, 0);
v_resultType_2999_ = lean_ctor_get(v_cases_2988_, 1);
v_discr_3000_ = lean_ctor_get(v_cases_2988_, 2);
v_alts_3001_ = lean_ctor_get(v_cases_2988_, 3);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_cases_2988_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3003_ = v_cases_2988_;
v_isShared_3004_ = v_isSharedCheck_3200_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_alts_3001_);
lean_inc(v_discr_3000_);
lean_inc(v_resultType_2999_);
lean_inc(v_typeName_2998_);
lean_dec(v_cases_2988_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3200_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v_subst_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = lean_st_ref_get(v_a_2379_);
v_subst_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc_ref(v_subst_3006_);
lean_dec(v___x_3005_);
v___x_3007_ = 0;
lean_inc(v_discr_3000_);
v___x_3008_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3006_, v_discr_3000_, v___x_2517_);
lean_dec_ref(v_subst_3006_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_fvarId_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3198_; 
v_fvarId_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3198_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_fvarId_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3198_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_st_ref_get(v_a_2379_);
v___x_3014_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_3001_);
lean_inc(v_fvarId_3009_);
v___x_3015_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3009_, v_currRecDepth_2504_, v_maxRecDepth_2505_, v___x_3014_, v_alts_3001_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3189_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3189_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3189_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_a_3016_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3180_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3180_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3180_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_subst_3025_; lean_object* v___x_3026_; lean_object* v___y_3028_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3085_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v_subst_3025_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_subst_3025_);
lean_dec(v___x_3013_);
lean_inc_ref(v_resultType_2999_);
v___x_3026_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3007_, v_subst_3025_, v___x_2517_, v_resultType_2999_);
lean_dec_ref(v_subst_3025_);
v___x_3116_ = lean_array_get_size(v_a_3021_);
v___x_3117_ = lean_nat_dec_eq(v___x_3116_, v___x_2596_);
if (v___x_3117_ == 0)
{
lean_del_object(v___x_2992_);
v___y_3091_ = v_a_2379_;
v___y_3092_ = v_a_2381_;
v___y_3093_ = v_a_2382_;
v___y_3094_ = v___x_2598_;
v___y_3095_ = v_a_2384_;
goto v___jp_3090_;
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_array_fget_borrowed(v_a_3021_, v___x_3014_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_params_3119_; lean_object* v_code_3120_; lean_object* v___y_3140_; lean_object* v___x_3149_; uint8_t v_a_3161_; uint8_t v___x_3162_; 
lean_del_object(v___x_2992_);
v_params_3119_ = lean_ctor_get(v___x_3118_, 1);
v_code_3120_ = lean_ctor_get(v___x_3118_, 2);
v___x_3149_ = lean_array_get_size(v_params_3119_);
v___x_3162_ = lean_nat_dec_lt(v___x_3014_, v___x_3149_);
if (v___x_3162_ == 0)
{
v_a_3161_ = v___x_2517_;
goto v___jp_3160_;
}
else
{
if (v___x_3162_ == 0)
{
v_a_3161_ = v___x_2517_;
goto v___jp_3160_;
}
else
{
size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = ((size_t)0ULL);
v___x_3164_ = lean_usize_of_nat(v___x_3149_);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_3119_, v___x_3163_, v___x_3164_, v_a_2379_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; uint8_t v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
v_a_3161_ = v___x_3167_;
goto v___jp_3160_;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_a_3168_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3165_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3165_);
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
}
v___jp_3121_:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2379_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3130_);
v___x_3124_ = v___x_3122_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_dec(v___x_3122_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v_code_3120_);
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_code_3120_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_code_3120_);
v_a_3131_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3122_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
v___jp_3139_:
{
if (lean_obj_tag(v___y_3140_) == 0)
{
lean_dec_ref(v___y_3140_);
goto v___jp_3121_;
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_code_3120_);
v_a_3141_ = lean_ctor_get(v___y_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___y_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___y_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___y_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
v___jp_3150_:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_lt(v___x_3014_, v___x_3149_);
if (v___x_3151_ == 0)
{
lean_dec_ref(v_params_3119_);
goto v___jp_3121_;
}
else
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_nat_dec_le(v___x_3149_, v___x_3149_);
if (v___x_3153_ == 0)
{
if (v___x_3151_ == 0)
{
lean_dec_ref(v_params_3119_);
goto v___jp_3121_;
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = lean_usize_of_nat(v___x_3149_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_params_3119_, v___x_3154_, v___x_3155_, v___x_3152_, v_a_2382_);
lean_dec_ref(v_params_3119_);
v___y_3140_ = v___x_3156_;
goto v___jp_3139_;
}
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3149_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_params_3119_, v___x_3157_, v___x_3158_, v___x_3152_, v_a_2382_);
lean_dec_ref(v_params_3119_);
v___y_3140_ = v___x_3159_;
goto v___jp_3139_;
}
}
}
v___jp_3160_:
{
if (v_a_3161_ == 0)
{
lean_inc_ref(v_code_3120_);
lean_inc_ref(v_params_3119_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
goto v___jp_3150_;
}
else
{
if (v___x_2517_ == 0)
{
v___y_3091_ = v_a_2379_;
v___y_3092_ = v_a_2381_;
v___y_3093_ = v_a_2382_;
v___y_3094_ = v___x_2598_;
v___y_3095_ = v_a_2384_;
goto v___jp_3090_;
}
else
{
lean_inc_ref(v_code_3120_);
lean_inc_ref(v_params_3119_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
goto v___jp_3150_;
}
}
}
}
else
{
lean_object* v_code_3176_; lean_object* v___x_3178_; 
lean_inc_ref(v___x_3118_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_code_3176_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_code_3176_);
lean_dec_ref(v___x_3118_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v_code_3176_);
v___x_3178_ = v___x_2992_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_code_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
v___jp_3027_:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_3028_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3039_; 
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3029_, 0);
lean_dec(v_unused_3040_);
v___x_3031_ = v___x_3029_;
v_isShared_3032_ = v_isSharedCheck_3039_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v___x_3029_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3039_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 6);
lean_ctor_set(v___x_3011_, 0, v___x_3026_);
v___x_3034_ = v___x_3011_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3026_);
v___x_3034_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3034_);
v___x_3036_ = v___x_3031_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
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
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3011_);
v_a_3041_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3029_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3029_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
v___jp_3049_:
{
if (lean_obj_tag(v___y_3051_) == 0)
{
lean_dec_ref(v___y_3051_);
v___y_3028_ = v___y_3050_;
goto v___jp_3027_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3011_);
v_a_3052_ = lean_ctor_get(v___y_3051_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___y_3051_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___y_3051_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___y_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
v___jp_3060_:
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_nat_dec_lt(v___x_3014_, v___y_3064_);
if (v___x_3067_ == 0)
{
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3061_);
lean_dec(v_a_3021_);
v___y_3028_ = v___y_3065_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_nat_dec_le(v___y_3064_, v___y_3064_);
if (v___x_3069_ == 0)
{
if (v___x_3067_ == 0)
{
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3061_);
lean_dec(v_a_3021_);
v___y_3028_ = v___y_3065_;
goto v___jp_3027_;
}
else
{
size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = ((size_t)0ULL);
v___x_3071_ = lean_usize_of_nat(v___y_3064_);
lean_dec(v___y_3064_);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_a_3021_, v___x_3070_, v___x_3071_, v___x_3068_, v___y_3063_, v___y_3062_, v___y_3061_, v___y_3066_);
lean_dec_ref(v___y_3061_);
lean_dec(v_a_3021_);
v___y_3050_ = v___y_3065_;
v___y_3051_ = v___x_3072_;
goto v___jp_3049_;
}
}
else
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___y_3064_);
lean_dec(v___y_3064_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_a_3021_, v___x_3073_, v___x_3074_, v___x_3068_, v___y_3063_, v___y_3062_, v___y_3061_, v___y_3066_);
lean_dec_ref(v___y_3061_);
lean_dec(v_a_3021_);
v___y_3050_ = v___y_3065_;
v___y_3051_ = v___x_3075_;
goto v___jp_3049_;
}
}
}
v___jp_3076_:
{
lean_object* v___x_3078_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 3, v_a_3021_);
lean_ctor_set(v___x_3003_, 2, v_fvarId_3009_);
lean_ctor_set(v___x_3003_, 1, v___x_3026_);
v___x_3078_ = v___x_3003_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_typeName_2998_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_fvarId_3009_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_a_3021_);
v___x_3078_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3079_);
v___x_3081_ = v___x_3023_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
v___jp_3084_:
{
if (v___y_3085_ == 0)
{
lean_del_object(v___x_3018_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_code_2377_);
goto v___jp_3076_;
}
else
{
uint8_t v___x_3086_; 
v___x_3086_ = l_Lean_instBEqFVarId_beq(v_discr_3000_, v_fvarId_3009_);
lean_dec(v_discr_3000_);
if (v___x_3086_ == 0)
{
lean_del_object(v___x_3018_);
lean_dec_ref(v_code_2377_);
goto v___jp_3076_;
}
else
{
lean_object* v___x_3088_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec(v_typeName_2998_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v_code_2377_);
v___x_3088_ = v___x_3018_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_code_2377_);
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
v___jp_3090_:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = lean_array_get_size(v_a_3021_);
v___x_3097_ = lean_nat_dec_lt(v___x_3014_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_del_object(v___x_3023_);
lean_del_object(v___x_3018_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3093_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3095_;
goto v___jp_3060_;
}
else
{
if (v___x_3097_ == 0)
{
lean_del_object(v___x_3023_);
lean_del_object(v___x_3018_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3093_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3095_;
goto v___jp_3060_;
}
else
{
size_t v___x_3098_; size_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = lean_usize_of_nat(v___x_3096_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_currRecDepth_2504_, v_maxRecDepth_2505_, v_a_3021_, v___x_3098_, v___x_3099_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
if (v___x_3100_ == 0)
{
lean_del_object(v___x_3023_);
lean_del_object(v___x_3018_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3093_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3095_;
goto v___jp_3060_;
}
else
{
if (v___x_2517_ == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v___y_3094_);
lean_del_object(v___x_3011_);
lean_inc(v_fvarId_3009_);
v___x_3101_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3009_, v___y_3091_);
if (lean_obj_tag(v___x_3101_) == 0)
{
size_t v___x_3102_; size_t v___x_3103_; uint8_t v___x_3104_; 
lean_dec_ref(v___x_3101_);
v___x_3102_ = lean_ptr_addr(v_alts_3001_);
lean_dec_ref(v_alts_3001_);
v___x_3103_ = lean_ptr_addr(v_a_3021_);
v___x_3104_ = lean_usize_dec_eq(v___x_3102_, v___x_3103_);
if (v___x_3104_ == 0)
{
lean_dec_ref(v_resultType_2999_);
v___y_3085_ = v___x_3104_;
goto v___jp_3084_;
}
else
{
size_t v___x_3105_; size_t v___x_3106_; uint8_t v___x_3107_; 
v___x_3105_ = lean_ptr_addr(v_resultType_2999_);
lean_dec_ref(v_resultType_2999_);
v___x_3106_ = lean_ptr_addr(v___x_3026_);
v___x_3107_ = lean_usize_dec_eq(v___x_3105_, v___x_3106_);
v___y_3085_ = v___x_3107_;
goto v___jp_3084_;
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_3023_);
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
v_a_3108_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3101_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3101_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_del_object(v___x_3023_);
lean_del_object(v___x_3018_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_dec_ref(v_code_2377_);
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3093_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3096_;
v___y_3065_ = v___y_3091_;
v___y_3066_ = v___y_3095_;
goto v___jp_3060_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_del_object(v___x_3018_);
lean_dec(v___x_3013_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_del_object(v___x_2992_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_a_3181_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3020_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3020_);
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
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v___x_3013_);
lean_del_object(v___x_3011_);
lean_dec(v_fvarId_3009_);
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_del_object(v___x_2992_);
lean_dec_ref(v_code_2377_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_a_3190_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3015_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3015_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
else
{
lean_object* v___x_3199_; 
lean_del_object(v___x_3003_);
lean_dec_ref(v_alts_3001_);
lean_dec(v_discr_3000_);
lean_dec_ref(v_resultType_2999_);
lean_dec(v_typeName_2998_);
lean_del_object(v___x_2992_);
lean_dec_ref(v_code_2377_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v___x_3199_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3007_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
lean_dec_ref(v___x_2598_);
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_code_2377_);
lean_dec_ref(v_cases_2988_);
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_a_3202_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_2989_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_2989_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
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
case 5:
{
lean_object* v_fvarId_3210_; lean_object* v___x_3211_; lean_object* v_subst_3212_; lean_object* v___x_3213_; 
lean_del_object(v___x_2520_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_fvarId_3210_ = lean_ctor_get(v_code_2377_, 0);
v___x_3211_ = lean_st_ref_get(v_a_2379_);
v_subst_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc_ref(v_subst_3212_);
lean_dec(v___x_3211_);
lean_inc(v_fvarId_3210_);
v___x_3213_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_3212_, v_fvarId_3210_, v___x_2517_);
lean_dec_ref(v_subst_3212_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_fvarId_3214_; lean_object* v___x_3215_; 
lean_dec_ref(v___x_2598_);
v_fvarId_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_n(v_fvarId_3214_, 2);
lean_dec_ref(v___x_3213_);
v___x_3215_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_3214_, v_a_2379_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3234_; 
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_3215_, 0);
lean_dec(v_unused_3235_);
v___x_3217_ = v___x_3215_;
v_isShared_3218_ = v_isSharedCheck_3234_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v___x_3215_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3234_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
uint8_t v___x_3219_; 
v___x_3219_ = l_Lean_instBEqFVarId_beq(v_fvarId_3210_, v_fvarId_3214_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3229_; 
v_isSharedCheck_3229_ = !lean_is_exclusive(v_code_2377_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_code_2377_, 0);
lean_dec(v_unused_3230_);
v___x_3221_ = v_code_2377_;
v_isShared_3222_ = v_isSharedCheck_3229_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v_code_2377_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3229_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v_fvarId_3214_);
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_fvarId_3214_);
v___x_3224_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3224_);
v___x_3226_ = v___x_3217_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v___x_3232_; 
lean_dec(v_fvarId_3214_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v_code_2377_);
v___x_3232_ = v___x_3217_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_code_2377_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_fvarId_3214_);
lean_dec_ref(v_code_2377_);
v_a_3236_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3215_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3215_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
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
uint8_t v___x_3244_; lean_object* v___x_3245_; 
lean_dec_ref(v_code_2377_);
v___x_3244_ = 0;
v___x_3245_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_3244_, v_a_2381_, v_a_2382_, v___x_2598_, v_a_2384_);
lean_dec_ref(v___x_2598_);
return v___x_3245_;
}
}
case 6:
{
lean_object* v_type_3246_; lean_object* v___x_3247_; lean_object* v_subst_3248_; uint8_t v___x_3249_; lean_object* v___x_3250_; size_t v___x_3251_; size_t v___x_3252_; uint8_t v___x_3253_; 
lean_dec_ref(v___x_2598_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_type_3246_ = lean_ctor_get(v_code_2377_, 0);
v___x_3247_ = lean_st_ref_get(v_a_2379_);
v_subst_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_subst_3248_);
lean_dec(v___x_3247_);
v___x_3249_ = 0;
lean_inc_ref(v_type_3246_);
v___x_3250_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3249_, v_subst_3248_, v___x_2517_, v_type_3246_);
lean_dec_ref(v_subst_3248_);
v___x_3251_ = lean_ptr_addr(v_type_3246_);
v___x_3252_ = lean_ptr_addr(v___x_3250_);
v___x_3253_ = lean_usize_dec_eq(v___x_3251_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3263_; 
v_isSharedCheck_3263_ = !lean_is_exclusive(v_code_2377_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v_code_2377_, 0);
lean_dec(v_unused_3264_);
v___x_3255_ = v_code_2377_;
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
else
{
lean_dec(v_code_2377_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3250_);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3250_);
v___x_3258_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3260_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_3258_);
v___x_3260_ = v___x_2520_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v___x_3266_; 
lean_dec_ref(v___x_3250_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_code_2377_);
v___x_3266_ = v___x_2520_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_code_2377_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
default: 
{
lean_object* v_decl_3268_; lean_object* v_k_3269_; 
lean_del_object(v___x_2520_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
v_decl_3268_ = lean_ctor_get(v_code_2377_, 0);
v_k_3269_ = lean_ctor_get(v_code_2377_, 1);
lean_inc_ref(v_k_3269_);
lean_inc_ref(v_decl_3268_);
v_decl_2523_ = v_decl_3268_;
v_k_2524_ = v_k_3269_;
v___y_2525_ = v_a_2378_;
v___y_2526_ = v_a_2379_;
v___y_2527_ = v_a_2380_;
v___y_2528_ = v_a_2381_;
v___y_2529_ = v_a_2382_;
v___y_2530_ = v___x_2598_;
v___y_2531_ = v_a_2384_;
goto v___jp_2522_;
}
}
v___jp_2522_:
{
lean_object* v_fvarId_2532_; lean_object* v_params_2533_; lean_object* v_type_2534_; lean_object* v___x_2535_; 
v_fvarId_2532_ = lean_ctor_get(v_decl_2523_, 0);
v_params_2533_ = lean_ctor_get(v_decl_2523_, 2);
v_type_2534_ = lean_ctor_get(v_decl_2523_, 3);
v___x_2535_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_2532_, v___y_2526_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; uint8_t v___x_2537_; uint8_t v___x_2538_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v___x_2537_ = 0;
v___x_2538_ = lean_unbox(v_a_2536_);
if (v___x_2538_ == 0)
{
uint8_t v___x_2539_; 
v___x_2539_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_2377_);
if (v___x_2539_ == 0)
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
v___y_2474_ = v___x_2540_;
v___y_2475_ = v_k_2524_;
v_decl_2476_ = v_decl_2523_;
v___y_2477_ = v___y_2525_;
v___y_2478_ = v___y_2526_;
v___y_2479_ = v___y_2527_;
v___y_2480_ = v___y_2528_;
v___y_2481_ = v___y_2529_;
v___y_2482_ = v___y_2530_;
v___y_2483_ = v___y_2531_;
goto v___jp_2473_;
}
else
{
uint8_t v___x_2541_; 
lean_inc_ref(v_type_2534_);
v___x_2541_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2534_, v_params_2533_);
if (v___x_2541_ == 0)
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
v___y_2474_ = v___x_2542_;
v___y_2475_ = v_k_2524_;
v_decl_2476_ = v_decl_2523_;
v___y_2477_ = v___y_2525_;
v___y_2478_ = v___y_2526_;
v___y_2479_ = v___y_2527_;
v___y_2480_ = v___y_2528_;
v___y_2481_ = v___y_2529_;
v___y_2482_ = v___y_2530_;
v___y_2483_ = v___y_2531_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2543_; lean_object* v_subst_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_st_ref_get(v___y_2526_);
v_subst_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_subst_2544_);
lean_dec(v___x_2543_);
v___x_2545_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2537_, v___x_2517_, v_decl_2523_, v_subst_2544_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec_ref(v_subst_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_a_2546_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_2526_);
if (lean_obj_tag(v___x_2549_) == 0)
{
uint8_t v___x_2550_; 
lean_dec_ref(v___x_2549_);
v___x_2550_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
v___y_2474_ = v___x_2550_;
v___y_2475_ = v_k_2524_;
v_decl_2476_ = v_a_2548_;
v___y_2477_ = v___y_2525_;
v___y_2478_ = v___y_2526_;
v___y_2479_ = v___y_2527_;
v___y_2480_ = v___y_2528_;
v___y_2481_ = v___y_2529_;
v___y_2482_ = v___y_2530_;
v___y_2483_ = v___y_2531_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2548_);
lean_dec(v_a_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_k_2524_);
lean_dec_ref(v_code_2377_);
v_a_2551_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2549_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2549_);
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
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_a_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_k_2524_);
lean_dec_ref(v_code_2377_);
v_a_2559_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2547_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2547_);
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
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_a_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_k_2524_);
lean_dec_ref(v_code_2377_);
v_a_2567_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2545_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2545_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
else
{
lean_object* v___x_2575_; lean_object* v_subst_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_st_ref_get(v___y_2526_);
v_subst_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_subst_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l_Lean_Compiler_LCNF_normFunDeclImp(v___x_2537_, v___x_2517_, v_decl_2523_, v_subst_2576_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec_ref(v_subst_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; uint8_t v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
v___y_2423_ = v___x_2579_;
v___y_2424_ = v_k_2524_;
v_decl_2425_ = v_a_2578_;
v___y_2426_ = v___y_2525_;
v___y_2427_ = v___y_2526_;
v___y_2428_ = v___y_2527_;
v___y_2429_ = v___y_2528_;
v___y_2430_ = v___y_2529_;
v___y_2431_ = v___y_2530_;
v___y_2432_ = v___y_2531_;
goto v___jp_2422_;
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_k_2524_);
lean_dec_ref(v_code_2377_);
v_a_2580_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2577_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2577_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_k_2524_);
lean_dec_ref(v_decl_2523_);
lean_dec_ref(v_code_2377_);
v_a_2588_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2535_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2535_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v_inheritedTraceOptions_2516_);
lean_dec(v_cancelTk_x3f_2514_);
lean_dec(v_currMacroScope_2512_);
lean_dec(v_quotContext_2511_);
lean_dec(v_maxHeartbeats_2510_);
lean_dec(v_initHeartbeats_2509_);
lean_dec(v_openDecls_2508_);
lean_dec(v_currNamespace_2507_);
lean_dec(v_ref_2506_);
lean_dec(v_maxRecDepth_2505_);
lean_dec(v_currRecDepth_2504_);
lean_dec_ref(v_options_2503_);
lean_dec_ref(v_fileMap_2502_);
lean_dec_ref(v_fileName_2501_);
lean_dec_ref(v_code_2377_);
v_a_3272_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_2518_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_2518_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref(v_code_2377_);
v___x_3280_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec_ref(v_a_2383_);
return v___x_3280_;
}
v___jp_2386_:
{
if (v___y_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref(v_code_2377_);
v___x_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___y_2387_);
lean_ctor_set(v___x_2390_, 1, v___y_2388_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; 
lean_dec_ref(v___y_2388_);
lean_dec_ref(v___y_2387_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_code_2377_);
return v___x_2392_;
}
}
v___jp_2393_:
{
if (v___y_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref(v_code_2377_);
v___x_2397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___y_2394_);
lean_ctor_set(v___x_2397_, 1, v___y_2395_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; 
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2394_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_code_2377_);
return v___x_2399_;
}
}
v___jp_2400_:
{
switch(lean_obj_tag(v_code_2377_))
{
case 1:
{
lean_object* v_decl_2403_; lean_object* v_k_2404_; size_t v___x_2405_; size_t v___x_2406_; uint8_t v___x_2407_; 
v_decl_2403_ = lean_ctor_get(v_code_2377_, 0);
v_k_2404_ = lean_ctor_get(v_code_2377_, 1);
v___x_2405_ = lean_ptr_addr(v_k_2404_);
v___x_2406_ = lean_ptr_addr(v___y_2402_);
v___x_2407_ = lean_usize_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___y_2402_;
v___y_2389_ = v___x_2407_;
goto v___jp_2386_;
}
else
{
size_t v___x_2408_; size_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = lean_ptr_addr(v_decl_2403_);
v___x_2409_ = lean_ptr_addr(v___y_2401_);
v___x_2410_ = lean_usize_dec_eq(v___x_2408_, v___x_2409_);
v___y_2387_ = v___y_2401_;
v___y_2388_ = v___y_2402_;
v___y_2389_ = v___x_2410_;
goto v___jp_2386_;
}
}
case 2:
{
lean_object* v_decl_2411_; lean_object* v_k_2412_; size_t v___x_2413_; size_t v___x_2414_; uint8_t v___x_2415_; 
v_decl_2411_ = lean_ctor_get(v_code_2377_, 0);
v_k_2412_ = lean_ctor_get(v_code_2377_, 1);
v___x_2413_ = lean_ptr_addr(v_k_2412_);
v___x_2414_ = lean_ptr_addr(v___y_2402_);
v___x_2415_ = lean_usize_dec_eq(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
v___y_2394_ = v___y_2401_;
v___y_2395_ = v___y_2402_;
v___y_2396_ = v___x_2415_;
goto v___jp_2393_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; uint8_t v___x_2418_; 
v___x_2416_ = lean_ptr_addr(v_decl_2411_);
v___x_2417_ = lean_ptr_addr(v___y_2401_);
v___x_2418_ = lean_usize_dec_eq(v___x_2416_, v___x_2417_);
v___y_2394_ = v___y_2401_;
v___y_2395_ = v___y_2402_;
v___y_2396_ = v___x_2418_;
goto v___jp_2393_;
}
}
default: 
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v_code_2377_);
v___x_2419_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
v___x_2420_ = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_2419_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
}
v___jp_2422_:
{
lean_object* v___x_2433_; 
lean_inc_ref(v___y_2431_);
v___x_2433_ = l_Lean_Compiler_LCNF_Simp_simp(v___y_2424_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v_fvarId_2435_; lean_object* v___x_2436_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v___x_2433_);
v_fvarId_2435_ = lean_ctor_get(v_decl_2425_, 0);
v___x_2436_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_2435_, v___y_2427_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; uint8_t v___x_2438_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = lean_unbox(v_a_2437_);
lean_dec(v_a_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_code_2377_);
v___x_2439_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2425_, v___y_2427_, v___y_2430_);
lean_dec_ref(v_decl_2425_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; 
v_unused_2447_ = lean_ctor_get(v___x_2439_, 0);
lean_dec(v_unused_2447_);
v___x_2441_ = v___x_2439_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_dec(v___x_2439_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v_a_2434_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2434_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_a_2434_);
v_a_2448_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2439_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2439_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
if (v___y_2423_ == 0)
{
lean_dec_ref(v___y_2431_);
v___y_2401_ = v_decl_2425_;
v___y_2402_ = v_a_2434_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2456_; 
lean_inc_ref(v_decl_2425_);
v___x_2456_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(v_decl_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec_ref(v___y_2431_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_dec_ref(v___x_2456_);
v___y_2401_ = v_decl_2425_;
v___y_2402_ = v_a_2434_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_a_2434_);
lean_dec_ref(v_decl_2425_);
lean_dec_ref(v_code_2377_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2434_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_decl_2425_);
lean_dec_ref(v_code_2377_);
v_a_2465_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2436_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2436_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_decl_2425_);
lean_dec_ref(v_code_2377_);
return v___x_2433_;
}
}
v___jp_2473_:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(v_decl_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref(v___x_2484_);
v___y_2423_ = v___y_2474_;
v___y_2424_ = v___y_2475_;
v_decl_2425_ = v_a_2485_;
v___y_2426_ = v___y_2477_;
v___y_2427_ = v___y_2478_;
v___y_2428_ = v___y_2479_;
v___y_2429_ = v___y_2480_;
v___y_2430_ = v___y_2481_;
v___y_2431_ = v___y_2482_;
v___y_2432_ = v___y_2483_;
goto v___jp_2422_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v_code_2377_);
v_a_2486_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2484_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
v___jp_2494_:
{
if (v___y_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v_code_2377_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___y_2495_);
lean_ctor_set(v___x_2498_, 1, v___y_2496_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; 
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2495_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_code_2377_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* v_decl_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_params_3290_; lean_object* v_type_3291_; lean_object* v_value_3292_; lean_object* v___x_3293_; lean_object* v_subst_3294_; uint8_t v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_params_3290_ = lean_ctor_get(v_decl_3281_, 2);
v_type_3291_ = lean_ctor_get(v_decl_3281_, 3);
v_value_3292_ = lean_ctor_get(v_decl_3281_, 4);
v___x_3293_ = lean_st_ref_get(v_a_3283_);
v_subst_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_ref(v_subst_3294_);
lean_dec(v___x_3293_);
v___x_3295_ = 0;
v___x_3296_ = 0;
lean_inc_ref(v_type_3291_);
v___x_3297_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_3295_, v_subst_3294_, v___x_3296_, v_type_3291_);
lean_dec_ref(v_subst_3294_);
lean_inc_ref(v_params_3290_);
v___x_3298_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_3295_, v___x_3296_, v_params_3290_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___x_3298_);
lean_inc_ref(v_a_3287_);
lean_inc_ref(v_value_3292_);
v___x_3300_ = l_Lean_Compiler_LCNF_Simp_simp(v_value_3292_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3302_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref(v___x_3300_);
v___x_3302_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3295_, v_decl_3281_, v___x_3297_, v_a_3299_, v_a_3301_, v_a_3286_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* v_fvarId_3329_, lean_object* v___x_3330_, lean_object* v___x_3331_, lean_object* v_i_3332_, lean_object* v_as_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_3329_, v___x_3330_, v___x_3331_, v_i_3332_, v_as_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___x_3331_);
lean_dec(v___x_3330_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* v_cases_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(v_cases_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* v_letDecl_3353_, lean_object* v_k_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(v_letDecl_3353_, v_k_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* v_code_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Compiler_LCNF_Simp_simp(v_code_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t v_pu_3374_, uint8_t v_t_3375_, lean_object* v_decl_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v_pu_3374_, v_t_3375_, v_decl_3376_, v___y_3378_, v___y_3381_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* v_pu_3386_, lean_object* v_t_3387_, lean_object* v_decl_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
uint8_t v_pu_boxed_3397_; uint8_t v_t_boxed_3398_; lean_object* v_res_3399_; 
v_pu_boxed_3397_ = lean_unbox(v_pu_3386_);
v_t_boxed_3398_ = lean_unbox(v_t_3387_);
v_res_3399_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(v_pu_boxed_3397_, v_t_boxed_3398_, v_decl_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t v_pu_3400_, uint8_t v_t_3401_, lean_object* v_args_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v_pu_3400_, v_t_3401_, v_args_3402_, v___y_3404_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* v_pu_3412_, lean_object* v_t_3413_, lean_object* v_args_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
uint8_t v_pu_boxed_3423_; uint8_t v_t_boxed_3424_; lean_object* v_res_3425_; 
v_pu_boxed_3423_ = lean_unbox(v_pu_3412_);
v_t_boxed_3424_ = lean_unbox(v_t_3413_);
v_res_3425_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(v_pu_boxed_3423_, v_t_boxed_3424_, v_args_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* v_inst_3426_, lean_object* v_R_3427_, lean_object* v_a_3428_, lean_object* v_b_3429_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_3428_, v_b_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* v_00_u03b2_3431_, lean_object* v_x_3432_, lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_3432_, v_x_3433_, v_x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* v_as_3436_, size_t v_i_3437_, size_t v_stop_3438_, lean_object* v_b_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_3436_, v_i_3437_, v_stop_3438_, v_b_3439_, v___y_3441_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* v_as_3449_, lean_object* v_i_3450_, lean_object* v_stop_3451_, lean_object* v_b_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
size_t v_i_boxed_3461_; size_t v_stop_boxed_3462_; lean_object* v_res_3463_; 
v_i_boxed_3461_ = lean_unbox_usize(v_i_3450_);
lean_dec(v_i_3450_);
v_stop_boxed_3462_ = lean_unbox_usize(v_stop_3451_);
lean_dec(v_stop_3451_);
v_res_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_3449_, v_i_boxed_3461_, v_stop_boxed_3462_, v_b_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v_as_3449_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* v_as_3464_, size_t v_i_3465_, size_t v_stop_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_3464_, v_i_3465_, v_stop_3466_, v___y_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* v_as_3476_, lean_object* v_i_3477_, lean_object* v_stop_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
size_t v_i_boxed_3487_; size_t v_stop_boxed_3488_; lean_object* v_res_3489_; 
v_i_boxed_3487_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_stop_boxed_3488_ = lean_unbox_usize(v_stop_3478_);
lean_dec(v_stop_3478_);
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_3476_, v_i_boxed_3487_, v_stop_boxed_3488_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_as_3476_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* v_as_3490_, size_t v_i_3491_, size_t v_stop_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_3490_, v_i_3491_, v_stop_3492_, v_b_3493_, v___y_3495_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* v_as_3500_, lean_object* v_i_3501_, lean_object* v_stop_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
size_t v_i_boxed_3509_; size_t v_stop_boxed_3510_; lean_object* v_res_3511_; 
v_i_boxed_3509_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_stop_boxed_3510_ = lean_unbox_usize(v_stop_3502_);
lean_dec(v_stop_3502_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_3500_, v_i_boxed_3509_, v_stop_boxed_3510_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_as_3500_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* v_as_3512_, size_t v_i_3513_, size_t v_stop_3514_, lean_object* v_b_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_3512_, v_i_3513_, v_stop_3514_, v_b_3515_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* v_as_3525_, lean_object* v_i_3526_, lean_object* v_stop_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
size_t v_i_boxed_3537_; size_t v_stop_boxed_3538_; lean_object* v_res_3539_; 
v_i_boxed_3537_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_stop_boxed_3538_ = lean_unbox_usize(v_stop_3527_);
lean_dec(v_stop_3527_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_3525_, v_i_boxed_3537_, v_stop_boxed_3538_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* v_as_3540_, size_t v_i_3541_, size_t v_stop_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_3540_, v_i_3541_, v_stop_3542_, v_b_3543_, v___y_3548_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* v_as_3553_, lean_object* v_i_3554_, lean_object* v_stop_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
size_t v_i_boxed_3565_; size_t v_stop_boxed_3566_; lean_object* v_res_3567_; 
v_i_boxed_3565_ = lean_unbox_usize(v_i_3554_);
lean_dec(v_i_3554_);
v_stop_boxed_3566_ = lean_unbox_usize(v_stop_3555_);
lean_dec(v_stop_3555_);
v_res_3567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_3553_, v_i_boxed_3565_, v_stop_boxed_3566_, v_b_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v_as_3553_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* v_as_3568_, size_t v_i_3569_, size_t v_stop_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_3568_, v_i_3569_, v_stop_3570_, v___y_3572_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* v_as_3580_, lean_object* v_i_3581_, lean_object* v_stop_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
size_t v_i_boxed_3591_; size_t v_stop_boxed_3592_; lean_object* v_res_3593_; 
v_i_boxed_3591_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_stop_boxed_3592_ = lean_unbox_usize(v_stop_3582_);
lean_dec(v_stop_3582_);
v_res_3593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_3580_, v_i_boxed_3591_, v_stop_boxed_3592_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v_as_3580_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* v_as_3594_, size_t v_sz_3595_, size_t v_i_3596_, lean_object* v_b_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_3594_, v_sz_3595_, v_i_3596_, v_b_3597_, v___y_3599_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* v_as_3607_, lean_object* v_sz_3608_, lean_object* v_i_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
size_t v_sz_boxed_3619_; size_t v_i_boxed_3620_; lean_object* v_res_3621_; 
v_sz_boxed_3619_ = lean_unbox_usize(v_sz_3608_);
lean_dec(v_sz_3608_);
v_i_boxed_3620_ = lean_unbox_usize(v_i_3609_);
lean_dec(v_i_3609_);
v_res_3621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_3607_, v_sz_boxed_3619_, v_i_boxed_3620_, v_b_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_as_3607_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_3622_, lean_object* v_x_3623_, size_t v_x_3624_, size_t v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_3623_, v_x_3624_, v_x_3625_, v_x_3626_, v_x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
size_t v_x_48568__boxed_3635_; size_t v_x_48569__boxed_3636_; lean_object* v_res_3637_; 
v_x_48568__boxed_3635_ = lean_unbox_usize(v_x_3631_);
lean_dec(v_x_3631_);
v_x_48569__boxed_3636_ = lean_unbox_usize(v_x_3632_);
lean_dec(v_x_3632_);
v_res_3637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_3629_, v_x_3630_, v_x_48568__boxed_3635_, v_x_48569__boxed_3636_, v_x_3633_, v_x_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t v_pu_3638_, uint8_t v_t_3639_, lean_object* v_i_3640_, lean_object* v_as_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_3638_, v_t_3639_, v_i_3640_, v_as_3641_, v___y_3643_, v___y_3646_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* v_pu_3651_, lean_object* v_t_3652_, lean_object* v_i_3653_, lean_object* v_as_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v_pu_boxed_3663_; uint8_t v_t_boxed_3664_; lean_object* v_res_3665_; 
v_pu_boxed_3663_ = lean_unbox(v_pu_3651_);
v_t_boxed_3664_ = lean_unbox(v_t_3652_);
v_res_3665_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_3663_, v_t_boxed_3664_, v_i_3653_, v_as_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3666_, lean_object* v_n_3667_, lean_object* v_k_3668_, lean_object* v_v_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_3667_, v_k_3668_, v_v_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3671_, size_t v_depth_3672_, lean_object* v_keys_3673_, lean_object* v_vals_3674_, lean_object* v_heq_3675_, lean_object* v_i_3676_, lean_object* v_entries_3677_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_3672_, v_keys_3673_, v_vals_3674_, v_i_3676_, v_entries_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3679_, lean_object* v_depth_3680_, lean_object* v_keys_3681_, lean_object* v_vals_3682_, lean_object* v_heq_3683_, lean_object* v_i_3684_, lean_object* v_entries_3685_){
_start:
{
size_t v_depth_boxed_3686_; lean_object* v_res_3687_; 
v_depth_boxed_3686_ = lean_unbox_usize(v_depth_3680_);
lean_dec(v_depth_3680_);
v_res_3687_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_3679_, v_depth_boxed_3686_, v_keys_3681_, v_vals_3682_, v_heq_3683_, v_i_3684_, v_entries_3685_);
lean_dec_ref(v_vals_3682_);
lean_dec_ref(v_keys_3681_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_3689_, v_x_3690_, v_x_3691_, v_x_3692_);
return v___x_3693_;
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
