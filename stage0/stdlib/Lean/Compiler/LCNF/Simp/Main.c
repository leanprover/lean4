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
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2_value;
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Subarray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_2;
goto _start;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_1 = x_4;
goto _start;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec_ref(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_7, x_12);
lean_dec_ref(x_7);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_1 = x_14;
goto _start;
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_1 = x_16;
goto _start;
}
default: 
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_13);
x_1 = x_18;
goto _start;
}
}
}
}
case 5:
{
uint8_t x_20; 
lean_dec_ref(x_1);
x_20 = 1;
return x_20;
}
default: 
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = 0;
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_instHashableFVarId_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_instHashableFVarId_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_instBEqFVarId_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_instBEqFVarId_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instHashableFVarId_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_instHashableFVarId_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_17 = lean_ctor_get(x_9, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_array_uget(x_1, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_fget(x_11, x_12);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_24);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_21, x_22);
lean_ctor_set(x_4, 1, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_9);
x_29 = lean_array_uget(x_1, x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_array_fget(x_11, x_12);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_12, x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_13);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_10, x_30, x_31);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = lean_array_uget(x_1, x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_array_fget(x_41, x_42);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_42, x_51);
lean_dec(x_42);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_43);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_40, x_49, x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_3, x_56);
x_3 = x_57;
x_4 = x_55;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_array_fget_borrowed(x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
x_20 = 0;
lean_inc_ref(x_19);
x_21 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_20, x_19, x_16, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 0;
x_24 = l_Lean_Compiler_LCNF_mkAuxParam(x_20, x_22, x_23, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_10, x_27);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_28);
x_29 = lean_array_push(x_15, x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_26);
x_31 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_16, x_18, x_30);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_29);
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_array_fget_borrowed(x_9, x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
x_44 = 0;
lean_inc_ref(x_43);
x_45 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_44, x_43, x_40, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = 0;
x_48 = l_Lean_Compiler_LCNF_mkAuxParam(x_44, x_46, x_47, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_10, x_51);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_52);
x_53 = lean_array_push(x_39, x_49);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_50);
x_55 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_40, x_42, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_2 = x_56;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_59 = x_48;
} else {
 lean_dec_ref(x_48);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = lean_ctor_get(x_1, 1);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_1);
x_67 = lean_nat_dec_lt(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_71 = x_2;
} else {
 lean_dec_ref(x_2);
 x_71 = lean_box(0);
}
x_72 = lean_array_fget_borrowed(x_64, x_65);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 2);
x_75 = 0;
lean_inc_ref(x_74);
x_76 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_75, x_74, x_70, x_67);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = 0;
x_79 = l_Lean_Compiler_LCNF_mkAuxParam(x_75, x_77, x_78, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_65, x_82);
lean_dec(x_65);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_64);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_66);
x_85 = lean_array_push(x_69, x_80);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_87 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_70, x_73, x_86);
if (lean_is_scalar(x_71)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_71;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_1 = x_84;
x_2 = x_88;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_91 = x_79;
} else {
 lean_dec_ref(x_79);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
x_93 = lean_ctor_get(x_76, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_94 = x_76;
} else {
 lean_dec_ref(x_76);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_15 = lean_array_get_size(x_12);
x_16 = l_Array_toSubarray___redArg(x_12, x_13, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_array_size(x_10);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_10, x_18, x_19, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_50; uint8_t x_51; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_50 = lean_array_get_size(x_10);
x_51 = lean_nat_dec_le(x_15, x_13);
if (x_51 == 0)
{
x_25 = x_15;
x_26 = x_50;
goto block_49;
}
else
{
x_25 = x_13;
x_26 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Array_toSubarray___redArg(x_10, x_25, x_26);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_22);
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_27, x_28, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = l_Lean_Compiler_LCNF_Code_internalize(x_33, x_11, x_32, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = 0;
lean_inc(x_35);
x_37 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_35, x_36, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_37);
x_38 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
x_39 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_31, x_35, x_38, x_5, x_6, x_7, x_8);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_20, 0);
lean_inc(x_53);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_3, x_4, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_11, x_1, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 1)
{
uint8_t x_15; 
lean_free_object(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_16, x_4, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec_ref(x_22);
x_23 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_24);
lean_dec(x_16);
x_25 = 0;
x_26 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_23, x_24, x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_14, 0, x_28);
lean_ctor_set(x_26, 0, x_14);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_14, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_14);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_dec_ref(x_41);
x_42 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_43);
lean_dec(x_16);
x_44 = 0;
x_45 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_42, x_43, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
lean_ctor_set(x_14, 0, x_46);
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_14);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_14);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_53 = x_41;
} else {
 lean_dec_ref(x_41);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_17);
if (x_55 == 0)
{
return x_17;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
lean_dec(x_17);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
lean_dec(x_14);
x_59 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_58, x_4, x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_unbox(x_60);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_63 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_61);
x_65 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
lean_dec_ref(x_65);
x_66 = lean_ctor_get(x_58, 2);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_58, 4);
lean_inc_ref(x_67);
lean_dec(x_58);
x_68 = 0;
x_69 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_66, x_67, x_2, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_70);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_80 = lean_ctor_get(x_59, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_83 = lean_box(0);
lean_ctor_set(x_12, 0, x_83);
return x_12;
}
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_12, 0);
lean_inc(x_84);
lean_dec(x_12);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_85, x_4, x_6);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_unbox(x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_91 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; 
lean_dec(x_89);
x_93 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_dec_ref(x_93);
x_94 = lean_ctor_get(x_85, 2);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_85, 4);
lean_inc_ref(x_95);
lean_dec(x_85);
x_96 = 0;
x_97 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_94, x_95, x_2, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_86;
}
lean_ctor_set(x_100, 0, x_98);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_86);
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_103 = x_97;
} else {
 lean_dec_ref(x_97);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_108 = lean_ctor_get(x_87, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_109 = x_87;
} else {
 lean_dec_ref(x_87);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_84);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_113 = !lean_is_exclusive(x_12);
if (x_113 == 0)
{
return x_12;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_12, 0);
lean_inc(x_114);
lean_dec(x_12);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_isInstanceReducibleCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 0);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 3)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_ctor_get(x_14, 2);
x_21 = lean_st_ref_get(x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = 0;
lean_inc(x_18);
x_24 = l_Lean_Environment_find_x3f(x_22, x_18, x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
x_27 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_26, x_8);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_free_object(x_27);
lean_inc(x_18);
x_32 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_18, x_8);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_free_object(x_32);
x_38 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_inc(x_18);
x_42 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_18, x_41, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_obj_tag(x_43) == 1)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_unbox(x_40);
lean_dec(x_40);
x_51 = l_Lean_Compiler_LCNF_Phase_toPurity(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_44);
x_52 = lean_array_get_size(x_20);
x_53 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_49);
lean_dec(x_49);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_43);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_38, 0, x_55);
return x_38;
}
else
{
lean_object* x_56; 
lean_free_object(x_38);
lean_inc_ref(x_17);
x_56 = l_Lean_Compiler_LCNF_mkNewParams(x_51, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_array_size(x_57);
x_59 = 0;
lean_inc(x_57);
x_60 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_58, x_59, x_57);
x_61 = l_Array_append___redArg(x_20, x_60);
lean_dec_ref(x_60);
lean_ctor_set(x_14, 2, x_61);
x_62 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_63 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_51, x_14, x_62, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_ctor_set_tag(x_34, 5);
lean_ctor_set(x_34, 0, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_34);
x_67 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_68 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_57, x_66, x_67, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_inc(x_16);
x_71 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_70, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec_ref(x_71);
x_72 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_43, 0, x_69);
lean_ctor_set(x_72, 0, x_43);
return x_72;
}
else
{
lean_object* x_75; 
lean_dec(x_72);
lean_ctor_set(x_43, 0, x_69);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_43);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_69);
lean_free_object(x_43);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_69);
lean_free_object(x_43);
lean_dec(x_6);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
return x_71;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_dec(x_71);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_free_object(x_43);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_68);
if (x_82 == 0)
{
return x_68;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_68, 0);
lean_inc(x_83);
lean_dec(x_68);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_57);
lean_free_object(x_43);
lean_free_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_63);
if (x_85 == 0)
{
return x_63;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_63, 0);
lean_inc(x_86);
lean_dec(x_63);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_free_object(x_43);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_56);
if (x_88 == 0)
{
return x_56;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_56, 0);
lean_inc(x_89);
lean_dec(x_56);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
}
else
{
lean_free_object(x_43);
lean_dec(x_49);
lean_free_object(x_38);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_47;
}
}
else
{
lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_43, 0);
lean_inc(x_91);
lean_dec(x_43);
x_92 = lean_unbox(x_40);
lean_dec(x_40);
x_93 = l_Lean_Compiler_LCNF_Phase_toPurity(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_44);
x_94 = lean_array_get_size(x_20);
x_95 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_91);
lean_dec(x_91);
x_96 = lean_nat_dec_lt(x_94, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_97 = lean_box(0);
lean_ctor_set(x_38, 0, x_97);
return x_38;
}
else
{
lean_object* x_98; 
lean_free_object(x_38);
lean_inc_ref(x_17);
x_98 = l_Lean_Compiler_LCNF_mkNewParams(x_93, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_array_size(x_99);
x_101 = 0;
lean_inc(x_99);
x_102 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_100, x_101, x_99);
x_103 = l_Array_append___redArg(x_20, x_102);
lean_dec_ref(x_102);
lean_ctor_set(x_14, 2, x_103);
x_104 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_105 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_93, x_14, x_104, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_ctor_set_tag(x_34, 5);
lean_ctor_set(x_34, 0, x_107);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_34);
x_109 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_110 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_99, x_108, x_109, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_inc(x_16);
x_113 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_112, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec_ref(x_113);
x_114 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_115 = x_114;
} else {
 lean_dec_ref(x_114);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_111);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_111);
lean_dec(x_6);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_110, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_125 = x_110;
} else {
 lean_dec_ref(x_110);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_99);
lean_free_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_127 = lean_ctor_get(x_105, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_128 = x_105;
} else {
 lean_dec_ref(x_105);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_98, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_131 = x_98;
} else {
 lean_dec_ref(x_98);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
return x_132;
}
}
}
else
{
lean_dec(x_91);
lean_free_object(x_38);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_47;
}
}
}
else
{
lean_dec(x_43);
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_47;
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_133; 
lean_free_object(x_38);
lean_dec(x_40);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_42);
if (x_133 == 0)
{
return x_42;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_42, 0);
lean_inc(x_134);
lean_dec(x_42);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_38, 0);
lean_inc(x_136);
lean_dec(x_38);
x_137 = lean_unbox(x_136);
lean_inc(x_18);
x_138 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_18, x_137, x_7, x_8);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_obj_tag(x_139) == 1)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_145 = x_139;
} else {
 lean_dec_ref(x_139);
 x_145 = lean_box(0);
}
x_146 = lean_unbox(x_136);
lean_dec(x_136);
x_147 = l_Lean_Compiler_LCNF_Phase_toPurity(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
lean_dec(x_140);
x_148 = lean_array_get_size(x_20);
x_149 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_144);
lean_dec(x_144);
x_150 = lean_nat_dec_lt(x_148, x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_145);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
else
{
lean_object* x_153; 
lean_inc_ref(x_17);
x_153 = l_Lean_Compiler_LCNF_mkNewParams(x_147, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_array_size(x_154);
x_156 = 0;
lean_inc(x_154);
x_157 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_155, x_156, x_154);
x_158 = l_Array_append___redArg(x_20, x_157);
lean_dec_ref(x_157);
lean_ctor_set(x_14, 2, x_158);
x_159 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_160 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_147, x_14, x_159, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_ctor_set_tag(x_34, 5);
lean_ctor_set(x_34, 0, x_162);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_34);
x_164 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_165 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_154, x_163, x_164, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_16);
x_168 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_167, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec_ref(x_168);
x_169 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_170 = x_169;
} else {
 lean_dec_ref(x_169);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_145;
}
lean_ctor_set(x_171, 0, x_166);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(0, 1, 0);
} else {
 x_172 = x_170;
}
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_166);
lean_dec(x_145);
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_174 = x_169;
} else {
 lean_dec_ref(x_169);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_166);
lean_dec(x_145);
lean_dec(x_6);
lean_dec_ref(x_1);
x_176 = lean_ctor_get(x_168, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_145);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_165, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_180 = x_165;
} else {
 lean_dec_ref(x_165);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_154);
lean_dec(x_145);
lean_free_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_160, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_183 = x_160;
} else {
 lean_dec_ref(x_160);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_145);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_153, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_186 = x_153;
} else {
 lean_dec_ref(x_153);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
}
else
{
lean_dec(x_145);
lean_dec(x_144);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_143;
}
}
else
{
lean_dec(x_139);
lean_dec(x_136);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_143;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_136);
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_188 = lean_ctor_get(x_138, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_189 = x_138;
} else {
 lean_dec_ref(x_138);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_191 = !lean_is_exclusive(x_38);
if (x_191 == 0)
{
return x_38;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_38, 0);
lean_inc(x_192);
lean_dec(x_38);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; 
lean_free_object(x_34);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_194 = lean_box(0);
lean_ctor_set(x_32, 0, x_194);
return x_32;
}
}
else
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_34, 0);
lean_inc(x_195);
lean_dec(x_34);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_free_object(x_32);
x_197 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_unbox(x_198);
lean_inc(x_18);
x_201 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_18, x_200, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_obj_tag(x_202) == 1)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_202, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
x_209 = lean_unbox(x_198);
lean_dec(x_198);
x_210 = l_Lean_Compiler_LCNF_Phase_toPurity(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_203);
x_211 = lean_array_get_size(x_20);
x_212 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_207);
lean_dec(x_207);
x_213 = lean_nat_dec_lt(x_211, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_208);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_214 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_215 = lean_alloc_ctor(0, 1, 0);
} else {
 x_215 = x_199;
}
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
else
{
lean_object* x_216; 
lean_dec(x_199);
lean_inc_ref(x_17);
x_216 = l_Lean_Compiler_LCNF_mkNewParams(x_210, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; size_t x_218; size_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = lean_array_size(x_217);
x_219 = 0;
lean_inc(x_217);
x_220 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_218, x_219, x_217);
x_221 = l_Array_append___redArg(x_20, x_220);
lean_dec_ref(x_220);
lean_ctor_set(x_14, 2, x_221);
x_222 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_223 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_210, x_14, x_222, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_226);
x_228 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_229 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_217, x_227, x_228, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec_ref(x_229);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_inc(x_16);
x_232 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_231, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
lean_dec_ref(x_232);
x_233 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_234 = x_233;
} else {
 lean_dec_ref(x_233);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_208;
}
lean_ctor_set(x_235, 0, x_230);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 1, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_230);
lean_dec(x_208);
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_230);
lean_dec(x_208);
lean_dec(x_6);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_241 = x_232;
} else {
 lean_dec_ref(x_232);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_208);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_243 = lean_ctor_get(x_229, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_244 = x_229;
} else {
 lean_dec_ref(x_229);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_217);
lean_dec(x_208);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_246 = lean_ctor_get(x_223, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_247 = x_223;
} else {
 lean_dec_ref(x_223);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_208);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_249 = lean_ctor_get(x_216, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_250 = x_216;
} else {
 lean_dec_ref(x_216);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
}
else
{
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_199);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_206;
}
}
else
{
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_198);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_206;
}
block_206:
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_box(0);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 1, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_199);
lean_dec(x_198);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_252 = lean_ctor_get(x_201, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_253 = x_201;
} else {
 lean_dec_ref(x_201);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_255 = lean_ctor_get(x_197, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_256 = x_197;
} else {
 lean_dec_ref(x_197);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_255);
return x_257;
}
}
else
{
lean_object* x_258; 
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_258 = lean_box(0);
lean_ctor_set(x_32, 0, x_258);
return x_32;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_259 = lean_ctor_get(x_32, 0);
lean_inc(x_259);
lean_dec(x_32);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_unbox(x_260);
lean_dec(x_260);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
x_266 = lean_unbox(x_264);
lean_inc(x_18);
x_267 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_18, x_266, x_7, x_8);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_269 = x_267;
} else {
 lean_dec_ref(x_267);
 x_269 = lean_box(0);
}
if (lean_obj_tag(x_268) == 1)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
x_275 = lean_unbox(x_264);
lean_dec(x_264);
x_276 = l_Lean_Compiler_LCNF_Phase_toPurity(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
lean_dec(x_269);
x_277 = lean_array_get_size(x_20);
x_278 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_273);
lean_dec(x_273);
x_279 = lean_nat_dec_lt(x_277, x_278);
lean_dec(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_274);
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_280 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_281 = lean_alloc_ctor(0, 1, 0);
} else {
 x_281 = x_265;
}
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
else
{
lean_object* x_282; 
lean_dec(x_265);
lean_inc_ref(x_17);
x_282 = l_Lean_Compiler_LCNF_mkNewParams(x_276, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; size_t x_284; size_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = lean_array_size(x_283);
x_285 = 0;
lean_inc(x_283);
x_286 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_284, x_285, x_283);
x_287 = l_Array_append___redArg(x_20, x_286);
lean_dec_ref(x_286);
lean_ctor_set(x_14, 2, x_287);
x_288 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_289 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_276, x_14, x_288, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
if (lean_is_scalar(x_261)) {
 x_292 = lean_alloc_ctor(5, 1, 0);
} else {
 x_292 = x_261;
 lean_ctor_set_tag(x_292, 5);
}
lean_ctor_set(x_292, 0, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_292);
x_294 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_295 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_283, x_293, x_294, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_inc(x_16);
x_298 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_297, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; 
lean_dec_ref(x_298);
x_299 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_300 = x_299;
} else {
 lean_dec_ref(x_299);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_274;
}
lean_ctor_set(x_301, 0, x_296);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_296);
lean_dec(x_274);
x_303 = lean_ctor_get(x_299, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_304 = x_299;
} else {
 lean_dec_ref(x_299);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_296);
lean_dec(x_274);
lean_dec(x_6);
lean_dec_ref(x_1);
x_306 = lean_ctor_get(x_298, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_307 = x_298;
} else {
 lean_dec_ref(x_298);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_274);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_309 = lean_ctor_get(x_295, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_310 = x_295;
} else {
 lean_dec_ref(x_295);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_283);
lean_dec(x_274);
lean_dec(x_261);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_312 = lean_ctor_get(x_289, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_313 = x_289;
} else {
 lean_dec_ref(x_289);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_274);
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_315 = lean_ctor_get(x_282, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_316 = x_282;
} else {
 lean_dec_ref(x_282);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
}
else
{
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_265);
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_272;
}
}
else
{
lean_dec(x_268);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_272;
}
block_272:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_box(0);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 1, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_318 = lean_ctor_get(x_267, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_319 = x_267;
} else {
 lean_dec_ref(x_267);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_321 = lean_ctor_get(x_263, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_322 = x_263;
} else {
 lean_dec_ref(x_263);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_261);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_324);
return x_325;
}
}
}
}
else
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_27, 0);
lean_inc(x_326);
lean_dec(x_27);
x_327 = lean_unbox(x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_inc(x_18);
x_330 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_18, x_8);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = lean_unbox(x_333);
lean_dec(x_333);
if (x_335 == 0)
{
lean_object* x_336; 
lean_dec(x_332);
x_336 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
x_339 = lean_unbox(x_337);
lean_inc(x_18);
x_340 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_18, x_339, x_7, x_8);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_342 = x_340;
} else {
 lean_dec_ref(x_340);
 x_342 = lean_box(0);
}
if (lean_obj_tag(x_341) == 1)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; uint8_t x_349; 
x_346 = lean_ctor_get(x_341, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_347 = x_341;
} else {
 lean_dec_ref(x_341);
 x_347 = lean_box(0);
}
x_348 = lean_unbox(x_337);
lean_dec(x_337);
x_349 = l_Lean_Compiler_LCNF_Phase_toPurity(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; uint8_t x_352; 
lean_dec(x_342);
x_350 = lean_array_get_size(x_20);
x_351 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_346);
lean_dec(x_346);
x_352 = lean_nat_dec_lt(x_350, x_351);
lean_dec(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_347);
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_353 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_354 = lean_alloc_ctor(0, 1, 0);
} else {
 x_354 = x_338;
}
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
else
{
lean_object* x_355; 
lean_dec(x_338);
lean_inc_ref(x_17);
x_355 = l_Lean_Compiler_LCNF_mkNewParams(x_349, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; size_t x_357; size_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
x_357 = lean_array_size(x_356);
x_358 = 0;
lean_inc(x_356);
x_359 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_357, x_358, x_356);
x_360 = l_Array_append___redArg(x_20, x_359);
lean_dec_ref(x_359);
lean_ctor_set(x_14, 2, x_360);
x_361 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_362 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_349, x_14, x_361, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_is_scalar(x_334)) {
 x_365 = lean_alloc_ctor(5, 1, 0);
} else {
 x_365 = x_334;
 lean_ctor_set_tag(x_365, 5);
}
lean_ctor_set(x_365, 0, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_365);
x_367 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_368 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_356, x_366, x_367, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_inc(x_16);
x_371 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_16, x_370, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
lean_dec_ref(x_371);
x_372 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_373 = x_372;
} else {
 lean_dec_ref(x_372);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_374 = x_347;
}
lean_ctor_set(x_374, 0, x_369);
if (lean_is_scalar(x_373)) {
 x_375 = lean_alloc_ctor(0, 1, 0);
} else {
 x_375 = x_373;
}
lean_ctor_set(x_375, 0, x_374);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_369);
lean_dec(x_347);
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_377 = x_372;
} else {
 lean_dec_ref(x_372);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_369);
lean_dec(x_347);
lean_dec(x_6);
lean_dec_ref(x_1);
x_379 = lean_ctor_get(x_371, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_380 = x_371;
} else {
 lean_dec_ref(x_371);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_347);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_382 = lean_ctor_get(x_368, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 x_383 = x_368;
} else {
 lean_dec_ref(x_368);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_356);
lean_dec(x_347);
lean_dec(x_334);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_385 = lean_ctor_get(x_362, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_386 = x_362;
} else {
 lean_dec_ref(x_362);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 1, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_347);
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_388 = lean_ctor_get(x_355, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 x_389 = x_355;
} else {
 lean_dec_ref(x_355);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
}
}
else
{
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_338);
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_345;
}
}
else
{
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_345;
}
block_345:
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_box(0);
if (lean_is_scalar(x_342)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_342;
}
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_391 = lean_ctor_get(x_340, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_392 = x_340;
} else {
 lean_dec_ref(x_340);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_394 = lean_ctor_get(x_336, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_395 = x_336;
} else {
 lean_dec_ref(x_336);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_334);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_397 = lean_box(0);
if (lean_is_scalar(x_332)) {
 x_398 = lean_alloc_ctor(0, 1, 0);
} else {
 x_398 = x_332;
}
lean_ctor_set(x_398, 0, x_397);
return x_398;
}
}
}
}
else
{
uint8_t x_399; 
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_399 = !lean_is_exclusive(x_27);
if (x_399 == 0)
{
return x_27;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_27, 0);
lean_inc(x_400);
lean_dec(x_27);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
return x_401;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; 
lean_dec(x_24);
lean_free_object(x_14);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_402 = lean_box(0);
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_402);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_404 = lean_ctor_get(x_1, 0);
x_405 = lean_ctor_get(x_1, 2);
x_406 = lean_ctor_get(x_14, 0);
x_407 = lean_ctor_get(x_14, 1);
x_408 = lean_ctor_get(x_14, 2);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_14);
x_409 = lean_st_ref_get(x_8);
x_410 = lean_ctor_get(x_409, 0);
lean_inc_ref(x_410);
lean_dec(x_409);
x_411 = 0;
lean_inc(x_406);
x_412 = l_Lean_Environment_find_x3f(x_410, x_406, x_411);
if (lean_obj_tag(x_412) == 1)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_414 = l_Lean_ConstantInfo_type(x_413);
lean_dec(x_413);
x_415 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_414, x_8);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
x_418 = lean_unbox(x_416);
lean_dec(x_416);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_419 = lean_box(0);
if (lean_is_scalar(x_417)) {
 x_420 = lean_alloc_ctor(0, 1, 0);
} else {
 x_420 = x_417;
}
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_dec(x_417);
lean_inc(x_406);
x_421 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_406, x_8);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 x_423 = x_421;
} else {
 lean_dec_ref(x_421);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 x_425 = x_422;
} else {
 lean_dec_ref(x_422);
 x_425 = lean_box(0);
}
x_426 = lean_unbox(x_424);
lean_dec(x_424);
if (x_426 == 0)
{
lean_object* x_427; 
lean_dec(x_423);
x_427 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = lean_unbox(x_428);
lean_inc(x_406);
x_431 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_406, x_430, x_7, x_8);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
if (lean_obj_tag(x_432) == 1)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_440; 
x_437 = lean_ctor_get(x_432, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 x_438 = x_432;
} else {
 lean_dec_ref(x_432);
 x_438 = lean_box(0);
}
x_439 = lean_unbox(x_428);
lean_dec(x_428);
x_440 = l_Lean_Compiler_LCNF_Phase_toPurity(x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; 
lean_dec(x_433);
x_441 = lean_array_get_size(x_408);
x_442 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_437);
lean_dec(x_437);
x_443 = lean_nat_dec_lt(x_441, x_442);
lean_dec(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_438);
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_444 = lean_box(0);
if (lean_is_scalar(x_429)) {
 x_445 = lean_alloc_ctor(0, 1, 0);
} else {
 x_445 = x_429;
}
lean_ctor_set(x_445, 0, x_444);
return x_445;
}
else
{
lean_object* x_446; 
lean_dec(x_429);
lean_inc_ref(x_405);
x_446 = l_Lean_Compiler_LCNF_mkNewParams(x_440, x_405, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; size_t x_448; size_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_448 = lean_array_size(x_447);
x_449 = 0;
lean_inc(x_447);
x_450 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_448, x_449, x_447);
x_451 = l_Array_append___redArg(x_408, x_450);
lean_dec_ref(x_450);
x_452 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_452, 0, x_406);
lean_ctor_set(x_452, 1, x_407);
lean_ctor_set(x_452, 2, x_451);
x_453 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_454 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_440, x_452, x_453, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec_ref(x_454);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
if (lean_is_scalar(x_425)) {
 x_457 = lean_alloc_ctor(5, 1, 0);
} else {
 x_457 = x_425;
 lean_ctor_set_tag(x_457, 5);
}
lean_ctor_set(x_457, 0, x_456);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_457);
x_459 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_460 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_447, x_458, x_459, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_inc(x_404);
x_463 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_404, x_462, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; 
lean_dec_ref(x_463);
x_464 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_465 = x_464;
} else {
 lean_dec_ref(x_464);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_466 = x_438;
}
lean_ctor_set(x_466, 0, x_461);
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(0, 1, 0);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_466);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_461);
lean_dec(x_438);
x_468 = lean_ctor_get(x_464, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_469 = x_464;
} else {
 lean_dec_ref(x_464);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 1, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_468);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_461);
lean_dec(x_438);
lean_dec(x_6);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_463, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 x_472 = x_463;
} else {
 lean_dec_ref(x_463);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_471);
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_438);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_474 = lean_ctor_get(x_460, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 x_475 = x_460;
} else {
 lean_dec_ref(x_460);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 1, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_474);
return x_476;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_447);
lean_dec(x_438);
lean_dec(x_425);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_477 = lean_ctor_get(x_454, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 x_478 = x_454;
} else {
 lean_dec_ref(x_454);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 1, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_477);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_438);
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_480 = lean_ctor_get(x_446, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_481 = x_446;
} else {
 lean_dec_ref(x_446);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 1, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_480);
return x_482;
}
}
}
else
{
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_429);
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_436;
}
}
else
{
lean_dec(x_432);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_436;
}
block_436:
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_box(0);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(0, 1, 0);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_483 = lean_ctor_get(x_431, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_484 = x_431;
} else {
 lean_dec_ref(x_431);
 x_484 = lean_box(0);
}
if (lean_is_scalar(x_484)) {
 x_485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_485 = x_484;
}
lean_ctor_set(x_485, 0, x_483);
return x_485;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_486 = lean_ctor_get(x_427, 0);
lean_inc(x_486);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_487 = x_427;
} else {
 lean_dec_ref(x_427);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 1, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_425);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_489 = lean_box(0);
if (lean_is_scalar(x_423)) {
 x_490 = lean_alloc_ctor(0, 1, 0);
} else {
 x_490 = x_423;
}
lean_ctor_set(x_490, 0, x_489);
return x_490;
}
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_491 = lean_ctor_get(x_415, 0);
lean_inc(x_491);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_492 = x_415;
} else {
 lean_dec_ref(x_415);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 1, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_491);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_412);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_494 = lean_box(0);
x_495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_495, 0, x_494);
return x_495;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_496 = lean_box(0);
x_497 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_497, 0, x_496);
return x_497;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_8, x_6, x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_free_object(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_instBEqFVarId_beq(x_12, x_2);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_instBEqFVarId_beq(x_15, x_2);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(x_9);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_st_ref_get(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_22, x_20, x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = l_Lean_instBEqFVarId_beq(x_25, x_2);
lean_dec(x_25);
x_28 = lean_box(x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(x_23);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_1);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_3 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
x_3 = lean_box(0);
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_mk_empty_array_with_capacity(x_2);
x_12 = lean_array_push(x_11, x_10);
lean_inc(x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_st_ref_get(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
lean_inc_ref(x_7);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_10, x_2, x_7);
lean_dec_ref(x_10);
lean_inc(x_8);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_1, x_12, x_8, x_2);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_1, x_3, x_13, x_14, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_7, x_8, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget_borrowed(x_4, x_3);
x_12 = lean_ctor_get(x_11, 2);
x_13 = lean_st_ref_get(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
lean_inc_ref(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_14, x_2, x_12);
lean_dec_ref(x_14);
lean_inc(x_11);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_1, x_11, x_15, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ptr_addr(x_11);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = lean_array_fset(x_4, x_3, x_17);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_3, x_25);
lean_dec(x_3);
x_3 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox(x_2);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg(x_1, x_2, x_12, x_3, x_5, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uget(x_1, x_2);
x_22 = l_Lean_Compiler_LCNF_Alt_getParams(x_21);
lean_dec(x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_20, x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
x_10 = x_24;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
if (x_25 == 0)
{
lean_dec_ref(x_22);
x_10 = x_24;
x_11 = lean_box(0);
goto block_15;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_23);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_22, x_27, x_28, x_24, x_6);
lean_dec_ref(x_22);
x_16 = x_29;
goto block_18;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_23);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_22, x_30, x_31, x_24, x_6);
lean_dec_ref(x_22);
x_16 = x_32;
goto block_18;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_4);
return x_33;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
block_18:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_10 = x_17;
x_11 = lean_box(0);
goto block_15;
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_5, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = lean_apply_9(x_2, x_5, x_3, x_1, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_4, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = lean_st_ref_take(x_5);
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_23);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_22, x_20, x_23);
lean_ctor_set(x_18, 0, x_24);
x_25 = lean_st_ref_set(x_5, x_18);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_10, x_26);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 2);
x_34 = lean_ctor_get(x_18, 3);
x_35 = lean_ctor_get_uint8(x_18, sizeof(void*)*7);
x_36 = lean_ctor_get(x_18, 4);
x_37 = lean_ctor_get(x_18, 5);
x_38 = lean_ctor_get(x_18, 6);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_39 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_39);
x_40 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_31, x_20, x_39);
x_41 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_36);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*7, x_35);
x_42 = lean_st_ref_set(x_5, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_10, x_43);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_44);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
lean_dec(x_4);
x_48 = lean_st_ref_take(x_5);
x_49 = lean_array_uget(x_1, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get_uint8(x_48, sizeof(void*)*7);
x_56 = lean_ctor_get(x_48, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 6);
lean_inc(x_58);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 lean_ctor_release(x_48, 6);
 x_59 = x_48;
} else {
 lean_dec_ref(x_48);
 x_59 = lean_box(0);
}
x_60 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_60);
x_61 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_51, x_50, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 7, 1);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
lean_ctor_set(x_62, 2, x_53);
lean_ctor_set(x_62, 3, x_54);
lean_ctor_set(x_62, 4, x_56);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_62, 6, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*7, x_55);
x_63 = lean_st_ref_set(x_5, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_10, x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_11);
x_67 = 1;
x_68 = lean_usize_add(x_3, x_67);
x_3 = x_68;
x_4 = x_66;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; lean_object* x_13; lean_object* x_15; 
x_7 = lean_nat_dec_eq(x_1, x_2);
x_8 = 1;
x_15 = lean_array_uget(x_3, x_4);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_13 = x_16;
goto block_14;
}
case 1:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_13 = x_17;
goto block_14;
}
default: 
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_15);
x_13 = x_18;
goto block_14;
}
}
block_12:
{
if (x_7 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
return x_8;
}
}
block_14:
{
if (lean_obj_tag(x_13) == 6)
{
lean_dec_ref(x_13);
goto block_12;
}
else
{
lean_dec_ref(x_13);
if (x_7 == 0)
{
return x_8;
}
else
{
goto block_12;
}
}
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_1, x_7, x_3, x_2);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_8, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_free_object(x_9);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; 
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
}
}
else
{
return x_9;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_free_object(x_9);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; 
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
}
}
else
{
return x_9;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(683u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_36; 
x_36 = lean_nat_dec_lt(x_1, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_8, x_10, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
x_38 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_1, x_7);
if (x_42 == 0)
{
lean_dec(x_7);
x_17 = x_1;
x_18 = x_2;
goto block_35;
}
else
{
lean_dec(x_1);
x_17 = x_7;
x_18 = x_2;
goto block_35;
}
}
block_35:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Array_toSubarray___redArg(x_5, x_17, x_18);
x_20 = l_Subarray_toArray___redArg(x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_23 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_6, x_21, x_22, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_25, x_10, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
x_28 = l_Lean_Compiler_LCNF_Simp_simp(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 2);
x_21 = lean_ctor_get(x_16, 3);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*4 + 2);
x_23 = lean_array_get_size(x_21);
x_24 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_16);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_12, 0);
lean_inc(x_194);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_194);
x_195 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_22, x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
x_197 = !lean_is_exclusive(x_3);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_3, 2);
x_199 = lean_ctor_get(x_3, 3);
lean_inc(x_194);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_194);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_199, x_194, x_196);
lean_ctor_set(x_3, 3, x_201);
lean_ctor_set(x_3, 2, x_200);
x_132 = x_3;
x_133 = x_4;
x_134 = x_5;
x_135 = x_6;
x_136 = x_7;
x_137 = x_8;
x_138 = x_9;
x_139 = lean_box(0);
goto block_193;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_3, 0);
x_203 = lean_ctor_get(x_3, 1);
x_204 = lean_ctor_get(x_3, 2);
x_205 = lean_ctor_get(x_3, 3);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_3);
lean_inc(x_194);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_194);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_205, x_194, x_196);
x_208 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_203);
lean_ctor_set(x_208, 2, x_206);
lean_ctor_set(x_208, 3, x_207);
x_132 = x_208;
x_133 = x_4;
x_134 = x_5;
x_135 = x_6;
x_136 = x_7;
x_137 = x_8;
x_138 = x_9;
x_139 = lean_box(0);
goto block_193;
}
}
else
{
uint8_t x_209; 
lean_dec(x_194);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_209 = !lean_is_exclusive(x_195);
if (x_209 == 0)
{
return x_195;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_195, 0);
lean_inc(x_210);
lean_dec(x_195);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
else
{
lean_dec(x_12);
x_132 = x_3;
x_133 = x_4;
x_134 = x_5;
x_135 = x_6;
x_136 = x_7;
x_137 = x_8;
x_138 = x_9;
x_139 = lean_box(0);
goto block_193;
}
block_131:
{
lean_object* x_40; 
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
lean_inc_ref(x_34);
lean_inc(x_30);
lean_inc_ref(x_38);
x_40 = l_Lean_Compiler_LCNF_Simp_simp(x_39, x_38, x_30, x_34, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_30);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec_ref(x_42);
lean_inc(x_41);
x_43 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec_ref(x_35);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
x_44 = l_Lean_Compiler_LCNF_inferAppType(x_32, x_20, x_29, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_45);
x_46 = l_Lean_Expr_headBeta(x_45);
x_47 = l_Lean_Expr_isForall(x_46);
lean_dec_ref(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_33);
x_48 = l_Lean_Compiler_LCNF_mkAuxParam(x_32, x_45, x_25, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
lean_inc(x_50);
x_51 = lean_apply_9(x_31, x_50, x_38, x_30, x_34, x_26, x_36, x_27, x_28, lean_box(0));
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_55 = lean_array_push(x_54, x_49);
x_56 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2));
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
x_57 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_32, x_55, x_52, x_56, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_53);
x_60 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_32, x_41, x_59, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_17)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_17;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_17)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_17;
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_58);
lean_dec(x_17);
x_69 = !lean_is_exclusive(x_60);
if (x_69 == 0)
{
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
lean_dec(x_60);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_72 = !lean_is_exclusive(x_57);
if (x_72 == 0)
{
return x_57;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_57, 0);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_75 = !lean_is_exclusive(x_51);
if (x_75 == 0)
{
return x_51;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_51, 0);
lean_inc(x_76);
lean_dec(x_51);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_41);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_78 = !lean_is_exclusive(x_48);
if (x_78 == 0)
{
return x_48;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
lean_dec(x_48);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_45);
x_81 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
x_82 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
x_83 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_81, x_41, x_82, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
x_85 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_84, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_36);
lean_inc_ref(x_26);
lean_inc_ref(x_34);
lean_inc(x_30);
lean_inc_ref(x_38);
lean_inc(x_87);
x_88 = lean_apply_9(x_31, x_87, x_38, x_30, x_34, x_26, x_36, x_27, x_28, lean_box(0));
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_86);
x_91 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_92 = lean_array_push(x_91, x_90);
x_93 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_92, x_89, x_38, x_30, x_34, x_26, x_36, x_27, x_28);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_36);
lean_dec_ref(x_26);
lean_dec_ref(x_34);
lean_dec(x_30);
lean_dec_ref(x_38);
lean_dec_ref(x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
if (lean_is_scalar(x_17)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_17;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
lean_dec(x_93);
if (lean_is_scalar(x_17)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_17;
}
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_17);
x_100 = !lean_is_exclusive(x_93);
if (x_100 == 0)
{
return x_93;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_86);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_103 = !lean_is_exclusive(x_88);
if (x_103 == 0)
{
return x_88;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_88, 0);
lean_inc(x_104);
lean_dec(x_88);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_106 = !lean_is_exclusive(x_85);
if (x_106 == 0)
{
return x_85;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
lean_dec(x_85);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_109 = !lean_is_exclusive(x_83);
if (x_109 == 0)
{
return x_83;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_83, 0);
lean_inc(x_110);
lean_dec(x_83);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_41);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_17);
x_112 = !lean_is_exclusive(x_44);
if (x_112 == 0)
{
return x_44;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_44, 0);
lean_inc(x_113);
lean_dec(x_44);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; 
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_20);
x_115 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_32, x_41, x_35, x_26, x_36, x_27, x_28);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
if (lean_is_scalar(x_17)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_17;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
lean_dec(x_115);
if (lean_is_scalar(x_17)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_17;
}
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_17);
x_122 = !lean_is_exclusive(x_115);
if (x_122 == 0)
{
return x_115;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_115, 0);
lean_inc(x_123);
lean_dec(x_115);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_41);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_20);
lean_dec(x_17);
x_125 = !lean_is_exclusive(x_42);
if (x_125 == 0)
{
return x_42;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_42, 0);
lean_inc(x_126);
lean_dec(x_42);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_20);
lean_dec(x_17);
x_128 = !lean_is_exclusive(x_40);
if (x_128 == 0)
{
return x_40;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_40, 0);
lean_inc(x_129);
lean_dec(x_40);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
block_193:
{
if (x_25 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_dec(x_16);
x_140 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc_ref(x_21);
x_141 = l_Array_toSubarray___redArg(x_21, x_140, x_24);
x_142 = l_Subarray_toArray___redArg(x_141);
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc_ref(x_142);
x_143 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_18, x_19, x_142, x_25, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
lean_dec_ref(x_18);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = 0;
x_146 = lean_box(x_145);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_24);
x_147 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(x_147, 0, x_24);
lean_closure_set(x_147, 1, x_23);
lean_closure_set(x_147, 2, x_11);
lean_closure_set(x_147, 3, x_2);
lean_closure_set(x_147, 4, x_21);
lean_closure_set(x_147, 5, x_146);
lean_closure_set(x_147, 6, x_140);
lean_inc_ref(x_134);
lean_inc_ref(x_132);
lean_inc_ref(x_147);
lean_inc(x_133);
x_148 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_148, 0, x_133);
lean_closure_set(x_148, 1, x_147);
lean_closure_set(x_148, 2, x_132);
lean_closure_set(x_148, 3, x_134);
x_149 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_2, x_11);
lean_dec(x_11);
lean_dec_ref(x_2);
if (x_149 == 0)
{
lean_dec(x_24);
x_26 = x_135;
x_27 = x_137;
x_28 = x_138;
x_29 = x_142;
x_30 = x_133;
x_31 = x_147;
x_32 = x_145;
x_33 = x_140;
x_34 = x_134;
x_35 = x_148;
x_36 = x_136;
x_37 = lean_box(0);
x_38 = x_132;
x_39 = x_144;
goto block_131;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_24);
if (x_150 == 0)
{
x_26 = x_135;
x_27 = x_137;
x_28 = x_138;
x_29 = x_142;
x_30 = x_133;
x_31 = x_147;
x_32 = x_145;
x_33 = x_140;
x_34 = x_134;
x_35 = x_148;
x_36 = x_136;
x_37 = lean_box(0);
x_38 = x_132;
x_39 = x_144;
goto block_131;
}
else
{
lean_object* x_151; 
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_142);
lean_dec_ref(x_20);
lean_dec(x_17);
x_151 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_133);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
lean_dec_ref(x_151);
x_152 = l_Lean_Compiler_LCNF_Simp_simp(x_144, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_152, 0, x_155);
return x_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_152, 0);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_152);
if (x_159 == 0)
{
return x_152;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
lean_dec(x_152);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_144);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
x_162 = !lean_is_exclusive(x_151);
if (x_162 == 0)
{
return x_151;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_151, 0);
lean_inc(x_163);
lean_dec(x_151);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
}
}
else
{
uint8_t x_165; 
lean_dec_ref(x_142);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_2);
x_165 = !lean_is_exclusive(x_143);
if (x_165 == 0)
{
return x_143;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_143, 0);
lean_inc(x_166);
lean_dec(x_143);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; 
lean_dec(x_24);
lean_dec(x_17);
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
x_168 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_16, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_170, x_133, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
lean_dec_ref(x_171);
x_172 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_133);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_172);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_2);
x_174 = l_Lean_Compiler_LCNF_Simp_simp(x_173, x_132, x_133, x_134, x_135, x_136, x_137, x_138);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_174, 0, x_177);
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
lean_dec(x_174);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_174);
if (x_181 == 0)
{
return x_174;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_174, 0);
lean_inc(x_182);
lean_dec(x_174);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_169);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_2);
x_184 = !lean_is_exclusive(x_172);
if (x_184 == 0)
{
return x_172;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_172, 0);
lean_inc(x_185);
lean_dec(x_172);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_169);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_2);
x_187 = !lean_is_exclusive(x_171);
if (x_187 == 0)
{
return x_171;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_171, 0);
lean_inc(x_188);
lean_dec(x_171);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_11);
lean_dec_ref(x_2);
x_190 = !lean_is_exclusive(x_168);
if (x_190 == 0)
{
return x_168;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_168, 0);
lean_inc(x_191);
lean_dec(x_168);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
}
}
else
{
lean_object* x_212; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_212 = lean_box(0);
lean_ctor_set(x_13, 0, x_212);
return x_13;
}
}
else
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_13, 0);
lean_inc(x_213);
lean_dec(x_13);
if (lean_obj_tag(x_213) == 1)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = lean_ctor_get(x_214, 2);
x_219 = lean_ctor_get(x_214, 3);
x_220 = lean_ctor_get_uint8(x_214, sizeof(void*)*4 + 2);
x_221 = lean_array_get_size(x_219);
x_222 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_214);
x_223 = lean_nat_dec_lt(x_221, x_222);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_12, 0);
lean_inc(x_381);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_381);
x_382 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_220, x_381, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
x_384 = lean_ctor_get(x_3, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_385);
x_386 = lean_ctor_get(x_3, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_387);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_388 = x_3;
} else {
 lean_dec_ref(x_3);
 x_388 = lean_box(0);
}
lean_inc(x_381);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_381);
lean_ctor_set(x_389, 1, x_386);
x_390 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_387, x_381, x_383);
if (lean_is_scalar(x_388)) {
 x_391 = lean_alloc_ctor(0, 4, 0);
} else {
 x_391 = x_388;
}
lean_ctor_set(x_391, 0, x_384);
lean_ctor_set(x_391, 1, x_385);
lean_ctor_set(x_391, 2, x_389);
lean_ctor_set(x_391, 3, x_390);
x_323 = x_391;
x_324 = x_4;
x_325 = x_5;
x_326 = x_6;
x_327 = x_7;
x_328 = x_8;
x_329 = x_9;
x_330 = lean_box(0);
goto block_380;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_381);
lean_dec(x_222);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_392 = lean_ctor_get(x_382, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_393 = x_382;
} else {
 lean_dec_ref(x_382);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_392);
return x_394;
}
}
else
{
lean_dec(x_12);
x_323 = x_3;
x_324 = x_4;
x_325 = x_5;
x_326 = x_6;
x_327 = x_7;
x_328 = x_8;
x_329 = x_9;
x_330 = lean_box(0);
goto block_380;
}
block_322:
{
lean_object* x_238; 
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
lean_inc_ref(x_232);
lean_inc(x_228);
lean_inc_ref(x_236);
x_238 = l_Lean_Compiler_LCNF_Simp_simp(x_237, x_236, x_228, x_232, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_228);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; 
lean_dec_ref(x_240);
lean_inc(x_239);
x_241 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_239);
if (x_241 == 0)
{
lean_object* x_242; 
lean_dec_ref(x_233);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
x_242 = l_Lean_Compiler_LCNF_inferAppType(x_230, x_218, x_227, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
lean_inc(x_243);
x_244 = l_Lean_Expr_headBeta(x_243);
x_245 = l_Lean_Expr_isForall(x_244);
lean_dec_ref(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
lean_dec(x_231);
x_246 = l_Lean_Compiler_LCNF_mkAuxParam(x_230, x_243, x_223, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
lean_inc(x_248);
x_249 = lean_apply_9(x_229, x_248, x_236, x_228, x_232, x_224, x_234, x_225, x_226, lean_box(0));
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_unsigned_to_nat(1u);
x_252 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0;
x_253 = lean_array_push(x_252, x_247);
x_254 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2));
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
x_255 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_230, x_253, x_250, x_254, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
lean_inc(x_256);
x_257 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_257, 0, x_256);
lean_closure_set(x_257, 1, x_251);
x_258 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_230, x_239, x_257, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_259);
if (lean_is_scalar(x_215)) {
 x_262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_262 = x_215;
}
lean_ctor_set(x_262, 0, x_261);
if (lean_is_scalar(x_260)) {
 x_263 = lean_alloc_ctor(0, 1, 0);
} else {
 x_263 = x_260;
}
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_256);
lean_dec(x_215);
x_264 = lean_ctor_get(x_258, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_265 = x_258;
} else {
 lean_dec_ref(x_258);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_267 = lean_ctor_get(x_255, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_268 = x_255;
} else {
 lean_dec_ref(x_255);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_247);
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_270 = lean_ctor_get(x_249, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_271 = x_249;
} else {
 lean_dec_ref(x_249);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_239);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_273 = lean_ctor_get(x_246, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_274 = x_246;
} else {
 lean_dec_ref(x_246);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_243);
x_276 = lean_mk_empty_array_with_capacity(x_231);
lean_dec(x_231);
x_277 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
x_278 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_276, x_239, x_277, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
x_280 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_279, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc(x_234);
lean_inc_ref(x_224);
lean_inc_ref(x_232);
lean_inc(x_228);
lean_inc_ref(x_236);
lean_inc(x_282);
x_283 = lean_apply_9(x_229, x_282, x_236, x_228, x_232, x_224, x_234, x_225, x_226, lean_box(0));
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec_ref(x_283);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_281);
x_286 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_287 = lean_array_push(x_286, x_285);
x_288 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_287, x_284, x_236, x_228, x_232, x_224, x_234, x_225, x_226);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_234);
lean_dec_ref(x_224);
lean_dec_ref(x_232);
lean_dec(x_228);
lean_dec_ref(x_236);
lean_dec_ref(x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_215;
}
lean_ctor_set(x_291, 0, x_289);
if (lean_is_scalar(x_290)) {
 x_292 = lean_alloc_ctor(0, 1, 0);
} else {
 x_292 = x_290;
}
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_215);
x_293 = lean_ctor_get(x_288, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_294 = x_288;
} else {
 lean_dec_ref(x_288);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_281);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_232);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_296 = lean_ctor_get(x_283, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_297 = x_283;
} else {
 lean_dec_ref(x_283);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_299 = lean_ctor_get(x_280, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_300 = x_280;
} else {
 lean_dec_ref(x_280);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_302 = lean_ctor_get(x_278, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_303 = x_278;
} else {
 lean_dec_ref(x_278);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_239);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec(x_215);
x_305 = lean_ctor_get(x_242, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_306 = x_242;
} else {
 lean_dec_ref(x_242);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
else
{
lean_object* x_308; 
lean_dec_ref(x_236);
lean_dec_ref(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_218);
x_308 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_230, x_239, x_233, x_224, x_234, x_225, x_226);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_310 = x_308;
} else {
 lean_dec_ref(x_308);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_311 = x_215;
}
lean_ctor_set(x_311, 0, x_309);
if (lean_is_scalar(x_310)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_310;
}
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_215);
x_313 = lean_ctor_get(x_308, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_314 = x_308;
} else {
 lean_dec_ref(x_308);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_239);
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_218);
lean_dec(x_215);
x_316 = lean_ctor_get(x_240, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_317 = x_240;
} else {
 lean_dec_ref(x_240);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 1, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec_ref(x_236);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec_ref(x_232);
lean_dec(x_231);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_218);
lean_dec(x_215);
x_319 = lean_ctor_get(x_238, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_320 = x_238;
} else {
 lean_dec_ref(x_238);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
}
block_380:
{
if (x_223 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_inc_ref(x_219);
lean_inc_ref(x_218);
lean_inc_ref(x_217);
lean_inc_ref(x_216);
lean_dec(x_214);
x_331 = lean_unsigned_to_nat(0u);
lean_inc(x_222);
lean_inc_ref(x_219);
x_332 = l_Array_toSubarray___redArg(x_219, x_331, x_222);
x_333 = l_Subarray_toArray___redArg(x_332);
lean_inc(x_329);
lean_inc_ref(x_328);
lean_inc(x_327);
lean_inc_ref(x_326);
lean_inc_ref(x_333);
x_334 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_216, x_217, x_333, x_223, x_323, x_324, x_325, x_326, x_327, x_328, x_329);
lean_dec_ref(x_216);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
lean_dec_ref(x_334);
x_336 = 0;
x_337 = lean_box(x_336);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_222);
x_338 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(x_338, 0, x_222);
lean_closure_set(x_338, 1, x_221);
lean_closure_set(x_338, 2, x_11);
lean_closure_set(x_338, 3, x_2);
lean_closure_set(x_338, 4, x_219);
lean_closure_set(x_338, 5, x_337);
lean_closure_set(x_338, 6, x_331);
lean_inc_ref(x_325);
lean_inc_ref(x_323);
lean_inc_ref(x_338);
lean_inc(x_324);
x_339 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_339, 0, x_324);
lean_closure_set(x_339, 1, x_338);
lean_closure_set(x_339, 2, x_323);
lean_closure_set(x_339, 3, x_325);
x_340 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_2, x_11);
lean_dec(x_11);
lean_dec_ref(x_2);
if (x_340 == 0)
{
lean_dec(x_222);
x_224 = x_326;
x_225 = x_328;
x_226 = x_329;
x_227 = x_333;
x_228 = x_324;
x_229 = x_338;
x_230 = x_336;
x_231 = x_331;
x_232 = x_325;
x_233 = x_339;
x_234 = x_327;
x_235 = lean_box(0);
x_236 = x_323;
x_237 = x_335;
goto block_322;
}
else
{
uint8_t x_341; 
x_341 = lean_nat_dec_eq(x_221, x_222);
lean_dec(x_222);
if (x_341 == 0)
{
x_224 = x_326;
x_225 = x_328;
x_226 = x_329;
x_227 = x_333;
x_228 = x_324;
x_229 = x_338;
x_230 = x_336;
x_231 = x_331;
x_232 = x_325;
x_233 = x_339;
x_234 = x_327;
x_235 = lean_box(0);
x_236 = x_323;
x_237 = x_335;
goto block_322;
}
else
{
lean_object* x_342; 
lean_dec_ref(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_333);
lean_dec_ref(x_218);
lean_dec(x_215);
x_342 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_324);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; 
lean_dec_ref(x_342);
x_343 = l_Lean_Compiler_LCNF_Simp_simp(x_335, x_323, x_324, x_325, x_326, x_327, x_328, x_329);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_344);
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(0, 1, 0);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_346);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_343, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_349 = x_343;
} else {
 lean_dec_ref(x_343);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_335);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
x_351 = lean_ctor_get(x_342, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_352 = x_342;
} else {
 lean_dec_ref(x_342);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec_ref(x_333);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_222);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_215);
lean_dec(x_11);
lean_dec_ref(x_2);
x_354 = lean_ctor_get(x_334, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_355 = x_334;
} else {
 lean_dec_ref(x_334);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
else
{
lean_object* x_357; 
lean_dec(x_222);
lean_dec(x_215);
lean_inc(x_329);
lean_inc_ref(x_328);
lean_inc(x_327);
lean_inc_ref(x_326);
x_357 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_214, x_323, x_324, x_325, x_326, x_327, x_328, x_329);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
lean_dec_ref(x_357);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_359, x_324, x_326, x_327, x_328, x_329);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; 
lean_dec_ref(x_360);
x_361 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_324);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_361);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_2);
x_363 = l_Lean_Compiler_LCNF_Simp_simp(x_362, x_323, x_324, x_325, x_326, x_327, x_328, x_329);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_364);
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(0, 1, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_369 = x_363;
} else {
 lean_dec_ref(x_363);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 1, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_358);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec_ref(x_2);
x_371 = lean_ctor_get(x_361, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_372 = x_361;
} else {
 lean_dec_ref(x_361);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_371);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_358);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec_ref(x_2);
x_374 = lean_ctor_get(x_360, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_375 = x_360;
} else {
 lean_dec_ref(x_360);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_374);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_11);
lean_dec_ref(x_2);
x_377 = lean_ctor_get(x_357, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_378 = x_357;
} else {
 lean_dec_ref(x_357);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_213);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_397 = !lean_is_exclusive(x_13);
if (x_397 == 0)
{
return x_13;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_13, 0);
lean_inc(x_398);
lean_dec(x_13);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_398);
return x_399;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_st_ref_get(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = 0;
lean_inc(x_10);
x_15 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_12, x_10, x_14);
lean_dec_ref(x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_17, x_4, x_6, x_8);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_24 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_21);
x_25 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_13, x_1, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set_tag(x_15, 4);
lean_ctor_set(x_15, 0, x_28);
x_29 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_13, x_15, x_6);
lean_dec_ref(x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec_ref(x_29);
x_30 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
if (lean_obj_tag(x_27) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_free_object(x_25);
x_31 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_32);
lean_dec_ref(x_27);
x_33 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_21);
x_59 = lean_ctor_get(x_33, 3);
lean_inc(x_59);
lean_dec_ref(x_33);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_34);
x_62 = lean_nat_dec_le(x_59, x_60);
if (x_62 == 0)
{
x_35 = x_59;
x_36 = x_61;
goto block_58;
}
else
{
lean_dec(x_59);
x_35 = x_60;
x_36 = x_61;
goto block_58;
}
block_58:
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_37 = l_Array_toSubarray___redArg(x_34, x_35, x_36);
x_38 = lean_array_size(x_31);
x_39 = 0;
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_31, x_38, x_39, x_37, x_3);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
lean_inc(x_6);
x_41 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_31, x_6);
lean_dec(x_6);
lean_dec_ref(x_31);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
if (lean_is_scalar(x_22)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_22;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
if (lean_is_scalar(x_22)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_22;
}
lean_ctor_set(x_47, 0, x_42);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_42);
lean_dec(x_22);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_31);
lean_dec(x_22);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_40, 0);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_64);
lean_dec_ref(x_27);
x_65 = !lean_is_exclusive(x_21);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_21, 0);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_eq(x_66, x_67);
if (x_68 == 1)
{
lean_object* x_69; 
lean_free_object(x_21);
lean_dec(x_66);
lean_dec_ref(x_63);
lean_free_object(x_25);
x_69 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_is_scalar(x_22)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_22;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
if (lean_is_scalar(x_22)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_22;
}
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_22);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
return x_69;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_66, x_79);
lean_dec(x_66);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_80);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_21);
x_82 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_83 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_81, x_82, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_array_get_borrowed(x_23, x_63, x_67);
x_86 = lean_ctor_get(x_85, 0);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_inc(x_86);
x_88 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_86, x_87, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec_ref(x_88);
lean_inc(x_6);
x_89 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_63, x_6);
lean_dec(x_6);
lean_dec_ref(x_63);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set(x_25, 1, x_90);
lean_ctor_set(x_25, 0, x_84);
if (lean_is_scalar(x_22)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_22;
}
lean_ctor_set(x_94, 0, x_25);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_91);
lean_ctor_set(x_25, 1, x_90);
lean_ctor_set(x_25, 0, x_84);
if (lean_is_scalar(x_22)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_22;
}
lean_ctor_set(x_95, 0, x_25);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_90);
lean_dec(x_84);
lean_free_object(x_25);
lean_dec(x_22);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
return x_91;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_84);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_6);
x_100 = !lean_is_exclusive(x_89);
if (x_100 == 0)
{
return x_89;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_89, 0);
lean_inc(x_101);
lean_dec(x_89);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_84);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = !lean_is_exclusive(x_88);
if (x_103 == 0)
{
return x_88;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_88, 0);
lean_inc(x_104);
lean_dec(x_88);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_106 = !lean_is_exclusive(x_83);
if (x_106 == 0)
{
return x_83;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_83, 0);
lean_inc(x_107);
lean_dec(x_83);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_21, 0);
lean_inc(x_109);
lean_dec(x_21);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_eq(x_109, x_110);
if (x_111 == 1)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec_ref(x_63);
lean_free_object(x_25);
x_112 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_22;
}
lean_ctor_set(x_115, 0, x_113);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_22);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_sub(x_109, x_120);
lean_dec(x_109);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_125 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_123, x_124, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_array_get_borrowed(x_23, x_63, x_110);
x_128 = lean_ctor_get(x_127, 0);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_inc(x_128);
x_130 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_128, x_129, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_dec_ref(x_130);
lean_inc(x_6);
x_131 = l_Lean_Compiler_LCNF_Simp_simp(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_63, x_6);
lean_dec(x_6);
lean_dec_ref(x_63);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_134 = x_133;
} else {
 lean_dec_ref(x_133);
 x_134 = lean_box(0);
}
lean_ctor_set(x_25, 1, x_132);
lean_ctor_set(x_25, 0, x_126);
if (lean_is_scalar(x_22)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_22;
}
lean_ctor_set(x_135, 0, x_25);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_126);
lean_free_object(x_25);
lean_dec(x_22);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_126);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_6);
x_140 = lean_ctor_get(x_131, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_141 = x_131;
} else {
 lean_dec_ref(x_131);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_126);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_free_object(x_25);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_146 = lean_ctor_get(x_125, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_147 = x_125;
} else {
 lean_dec_ref(x_125);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_free_object(x_25);
lean_dec(x_21);
x_149 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_149);
lean_dec_ref(x_27);
x_150 = l_Lean_Compiler_LCNF_Simp_simp(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 0);
if (lean_is_scalar(x_22)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_22;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_150, 0, x_153);
return x_150;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
lean_dec(x_150);
if (lean_is_scalar(x_22)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_22;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
else
{
uint8_t x_157; 
lean_dec(x_22);
x_157 = !lean_is_exclusive(x_150);
if (x_157 == 0)
{
return x_150;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
lean_dec(x_150);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
}
else
{
uint8_t x_160; 
lean_free_object(x_25);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_160 = !lean_is_exclusive(x_30);
if (x_160 == 0)
{
return x_30;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_30, 0);
lean_inc(x_161);
lean_dec(x_30);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_free_object(x_25);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_163 = !lean_is_exclusive(x_29);
if (x_163 == 0)
{
return x_29;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_29, 0);
lean_inc(x_164);
lean_dec(x_29);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_25, 0);
x_167 = lean_ctor_get(x_25, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_25);
lean_ctor_set_tag(x_15, 4);
lean_ctor_set(x_15, 0, x_167);
x_168 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_13, x_15, x_6);
lean_dec_ref(x_15);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec_ref(x_168);
x_169 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_169) == 0)
{
lean_dec_ref(x_169);
if (lean_obj_tag(x_166) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_166, 2);
lean_inc_ref(x_171);
lean_dec_ref(x_166);
x_172 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_173);
lean_dec_ref(x_21);
x_196 = lean_ctor_get(x_172, 3);
lean_inc(x_196);
lean_dec_ref(x_172);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_array_get_size(x_173);
x_199 = lean_nat_dec_le(x_196, x_197);
if (x_199 == 0)
{
x_174 = x_196;
x_175 = x_198;
goto block_195;
}
else
{
lean_dec(x_196);
x_174 = x_197;
x_175 = x_198;
goto block_195;
}
block_195:
{
lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; 
x_176 = l_Array_toSubarray___redArg(x_173, x_174, x_175);
x_177 = lean_array_size(x_170);
x_178 = 0;
x_179 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_170, x_177, x_178, x_176, x_3);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec_ref(x_179);
lean_inc(x_6);
x_180 = l_Lean_Compiler_LCNF_Simp_simp(x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_170, x_6);
lean_dec(x_6);
lean_dec_ref(x_170);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_183 = x_182;
} else {
 lean_dec_ref(x_182);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_22;
}
lean_ctor_set(x_184, 0, x_181);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_181);
lean_dec(x_22);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_170);
lean_dec(x_22);
lean_dec(x_6);
x_189 = lean_ctor_get(x_180, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_190 = x_180;
} else {
 lean_dec_ref(x_180);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_192 = lean_ctor_get(x_179, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_193 = x_179;
} else {
 lean_dec_ref(x_179);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_166, 2);
lean_inc_ref(x_201);
lean_dec_ref(x_166);
x_202 = lean_ctor_get(x_21, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_203 = x_21;
} else {
 lean_dec_ref(x_21);
 x_203 = lean_box(0);
}
x_204 = lean_unsigned_to_nat(0u);
x_205 = lean_nat_dec_eq(x_202, x_204);
if (x_205 == 1)
{
lean_object* x_206; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_200);
x_206 = l_Lean_Compiler_LCNF_Simp_simp(x_201, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_22;
}
lean_ctor_set(x_209, 0, x_207);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_22);
x_211 = lean_ctor_get(x_206, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_212 = x_206;
} else {
 lean_dec_ref(x_206);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_sub(x_202, x_214);
lean_dec(x_202);
if (lean_is_scalar(x_203)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_203;
 lean_ctor_set_tag(x_216, 0);
}
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_218 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_219 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_217, x_218, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_array_get_borrowed(x_23, x_200, x_204);
x_222 = lean_ctor_get(x_221, 0);
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
lean_inc(x_222);
x_224 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_222, x_223, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; 
lean_dec_ref(x_224);
lean_inc(x_6);
x_225 = l_Lean_Compiler_LCNF_Simp_simp(x_201, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_200, x_6);
lean_dec(x_6);
lean_dec_ref(x_200);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_228 = x_227;
} else {
 lean_dec_ref(x_227);
 x_228 = lean_box(0);
}
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_226);
if (lean_is_scalar(x_22)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_22;
}
lean_ctor_set(x_230, 0, x_229);
if (lean_is_scalar(x_228)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_228;
}
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_226);
lean_dec(x_220);
lean_dec(x_22);
x_232 = lean_ctor_get(x_227, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_233 = x_227;
} else {
 lean_dec_ref(x_227);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_220);
lean_dec_ref(x_200);
lean_dec(x_22);
lean_dec(x_6);
x_235 = lean_ctor_get(x_225, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_236 = x_225;
} else {
 lean_dec_ref(x_225);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_220);
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_238 = lean_ctor_get(x_224, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_239 = x_224;
} else {
 lean_dec_ref(x_224);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_241 = lean_ctor_get(x_219, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_242 = x_219;
} else {
 lean_dec_ref(x_219);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_21);
x_244 = lean_ctor_get(x_166, 0);
lean_inc_ref(x_244);
lean_dec_ref(x_166);
x_245 = l_Lean_Compiler_LCNF_Simp_simp(x_244, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_22;
}
lean_ctor_set(x_248, 0, x_246);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 1, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_22);
x_250 = lean_ctor_get(x_245, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_251 = x_245;
} else {
 lean_dec_ref(x_245);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_166);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_253 = lean_ctor_get(x_169, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_254 = x_169;
} else {
 lean_dec_ref(x_169);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_166);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_256 = lean_ctor_get(x_168, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_257 = x_168;
} else {
 lean_dec_ref(x_168);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
}
else
{
lean_object* x_259; 
lean_dec(x_20);
lean_free_object(x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_259 = lean_box(0);
lean_ctor_set(x_18, 0, x_259);
return x_18;
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_18, 0);
lean_inc(x_260);
lean_dec(x_18);
if (lean_obj_tag(x_260) == 1)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_262 = x_260;
} else {
 lean_dec_ref(x_260);
 x_262 = lean_box(0);
}
x_263 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_264 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_261);
x_265 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_13, x_1, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
lean_ctor_set_tag(x_15, 4);
lean_ctor_set(x_15, 0, x_267);
x_269 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_13, x_15, x_6);
lean_dec_ref(x_15);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
lean_dec_ref(x_269);
x_270 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
if (lean_obj_tag(x_266) == 0)
{
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_dec(x_268);
x_271 = lean_ctor_get(x_266, 1);
lean_inc_ref(x_271);
x_272 = lean_ctor_get(x_266, 2);
lean_inc_ref(x_272);
lean_dec_ref(x_266);
x_273 = lean_ctor_get(x_261, 0);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_261, 1);
lean_inc_ref(x_274);
lean_dec_ref(x_261);
x_297 = lean_ctor_get(x_273, 3);
lean_inc(x_297);
lean_dec_ref(x_273);
x_298 = lean_unsigned_to_nat(0u);
x_299 = lean_array_get_size(x_274);
x_300 = lean_nat_dec_le(x_297, x_298);
if (x_300 == 0)
{
x_275 = x_297;
x_276 = x_299;
goto block_296;
}
else
{
lean_dec(x_297);
x_275 = x_298;
x_276 = x_299;
goto block_296;
}
block_296:
{
lean_object* x_277; size_t x_278; size_t x_279; lean_object* x_280; 
x_277 = l_Array_toSubarray___redArg(x_274, x_275, x_276);
x_278 = lean_array_size(x_271);
x_279 = 0;
x_280 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_271, x_278, x_279, x_277, x_3);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
lean_dec_ref(x_280);
lean_inc(x_6);
x_281 = l_Lean_Compiler_LCNF_Simp_simp(x_272, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_271, x_6);
lean_dec(x_6);
lean_dec_ref(x_271);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_284 = x_283;
} else {
 lean_dec_ref(x_283);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_285 = x_262;
}
lean_ctor_set(x_285, 0, x_282);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_282);
lean_dec(x_262);
x_287 = lean_ctor_get(x_283, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 x_288 = x_283;
} else {
 lean_dec_ref(x_283);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec_ref(x_271);
lean_dec(x_262);
lean_dec(x_6);
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_291 = x_281;
} else {
 lean_dec_ref(x_281);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_272);
lean_dec_ref(x_271);
lean_dec(x_262);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_293 = lean_ctor_get(x_280, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_294 = x_280;
} else {
 lean_dec_ref(x_280);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_301 = lean_ctor_get(x_266, 1);
lean_inc_ref(x_301);
x_302 = lean_ctor_get(x_266, 2);
lean_inc_ref(x_302);
lean_dec_ref(x_266);
x_303 = lean_ctor_get(x_261, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_304 = x_261;
} else {
 lean_dec_ref(x_261);
 x_304 = lean_box(0);
}
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_nat_dec_eq(x_303, x_305);
if (x_306 == 1)
{
lean_object* x_307; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec_ref(x_301);
lean_dec(x_268);
x_307 = l_Lean_Compiler_LCNF_Simp_simp(x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_262;
}
lean_ctor_set(x_310, 0, x_308);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(0, 1, 0);
} else {
 x_311 = x_309;
}
lean_ctor_set(x_311, 0, x_310);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_262);
x_312 = lean_ctor_get(x_307, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_313 = x_307;
} else {
 lean_dec_ref(x_307);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = lean_unsigned_to_nat(1u);
x_316 = lean_nat_sub(x_303, x_315);
lean_dec(x_303);
if (lean_is_scalar(x_304)) {
 x_317 = lean_alloc_ctor(0, 1, 0);
} else {
 x_317 = x_304;
 lean_ctor_set_tag(x_317, 0);
}
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_320 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_318, x_319, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = lean_array_get_borrowed(x_263, x_301, x_305);
x_323 = lean_ctor_get(x_322, 0);
x_324 = lean_ctor_get(x_321, 0);
lean_inc(x_324);
lean_inc(x_323);
x_325 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_323, x_324, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; 
lean_dec_ref(x_325);
lean_inc(x_6);
x_326 = l_Lean_Compiler_LCNF_Simp_simp(x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec_ref(x_326);
x_328 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_301, x_6);
lean_dec(x_6);
lean_dec_ref(x_301);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_329 = x_328;
} else {
 lean_dec_ref(x_328);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_268;
}
lean_ctor_set(x_330, 0, x_321);
lean_ctor_set(x_330, 1, x_327);
if (lean_is_scalar(x_262)) {
 x_331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_331 = x_262;
}
lean_ctor_set(x_331, 0, x_330);
if (lean_is_scalar(x_329)) {
 x_332 = lean_alloc_ctor(0, 1, 0);
} else {
 x_332 = x_329;
}
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_327);
lean_dec(x_321);
lean_dec(x_268);
lean_dec(x_262);
x_333 = lean_ctor_get(x_328, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_334 = x_328;
} else {
 lean_dec_ref(x_328);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_321);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_262);
lean_dec(x_6);
x_336 = lean_ctor_get(x_326, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_337 = x_326;
} else {
 lean_dec_ref(x_326);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_321);
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_262);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_339 = lean_ctor_get(x_325, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_340 = x_325;
} else {
 lean_dec_ref(x_325);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_268);
lean_dec(x_262);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_342 = lean_ctor_get(x_320, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_343 = x_320;
} else {
 lean_dec_ref(x_320);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_268);
lean_dec(x_261);
x_345 = lean_ctor_get(x_266, 0);
lean_inc_ref(x_345);
lean_dec_ref(x_266);
x_346 = l_Lean_Compiler_LCNF_Simp_simp(x_345, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_262;
}
lean_ctor_set(x_349, 0, x_347);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 1, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_262);
x_351 = lean_ctor_get(x_346, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_352 = x_346;
} else {
 lean_dec_ref(x_346);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_354 = lean_ctor_get(x_270, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_355 = x_270;
} else {
 lean_dec_ref(x_270);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_357 = lean_ctor_get(x_269, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_358 = x_269;
} else {
 lean_dec_ref(x_269);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_260);
lean_free_object(x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_360 = lean_box(0);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_360);
return x_361;
}
}
}
else
{
uint8_t x_362; 
lean_free_object(x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = !lean_is_exclusive(x_18);
if (x_362 == 0)
{
return x_18;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_18, 0);
lean_inc(x_363);
lean_dec(x_18);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_15, 0);
lean_inc(x_365);
lean_dec(x_15);
x_366 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_365, x_4, x_6, x_8);
lean_dec(x_365);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_367) == 1)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_368);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
x_371 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0;
x_372 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_369);
x_373 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_13, x_1, x_372);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_377, 0, x_375);
x_378 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_13, x_377, x_6);
lean_dec_ref(x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
lean_dec_ref(x_378);
x_379 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_379) == 0)
{
lean_dec_ref(x_379);
if (lean_obj_tag(x_374) == 0)
{
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_376);
x_380 = lean_ctor_get(x_374, 1);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_374, 2);
lean_inc_ref(x_381);
lean_dec_ref(x_374);
x_382 = lean_ctor_get(x_369, 0);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_369, 1);
lean_inc_ref(x_383);
lean_dec_ref(x_369);
x_406 = lean_ctor_get(x_382, 3);
lean_inc(x_406);
lean_dec_ref(x_382);
x_407 = lean_unsigned_to_nat(0u);
x_408 = lean_array_get_size(x_383);
x_409 = lean_nat_dec_le(x_406, x_407);
if (x_409 == 0)
{
x_384 = x_406;
x_385 = x_408;
goto block_405;
}
else
{
lean_dec(x_406);
x_384 = x_407;
x_385 = x_408;
goto block_405;
}
block_405:
{
lean_object* x_386; size_t x_387; size_t x_388; lean_object* x_389; 
x_386 = l_Array_toSubarray___redArg(x_383, x_384, x_385);
x_387 = lean_array_size(x_380);
x_388 = 0;
x_389 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_380, x_387, x_388, x_386, x_3);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
lean_dec_ref(x_389);
lean_inc(x_6);
x_390 = l_Lean_Compiler_LCNF_Simp_simp(x_381, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_380, x_6);
lean_dec(x_6);
lean_dec_ref(x_380);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_393 = x_392;
} else {
 lean_dec_ref(x_392);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_370;
}
lean_ctor_set(x_394, 0, x_391);
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(0, 1, 0);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_391);
lean_dec(x_370);
x_396 = lean_ctor_get(x_392, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_397 = x_392;
} else {
 lean_dec_ref(x_392);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 1, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec_ref(x_380);
lean_dec(x_370);
lean_dec(x_6);
x_399 = lean_ctor_get(x_390, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_400 = x_390;
} else {
 lean_dec_ref(x_390);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 1, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_370);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_402 = lean_ctor_get(x_389, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_403 = x_389;
} else {
 lean_dec_ref(x_389);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_402);
return x_404;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_410 = lean_ctor_get(x_374, 1);
lean_inc_ref(x_410);
x_411 = lean_ctor_get(x_374, 2);
lean_inc_ref(x_411);
lean_dec_ref(x_374);
x_412 = lean_ctor_get(x_369, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_413 = x_369;
} else {
 lean_dec_ref(x_369);
 x_413 = lean_box(0);
}
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_nat_dec_eq(x_412, x_414);
if (x_415 == 1)
{
lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec_ref(x_410);
lean_dec(x_376);
x_416 = l_Lean_Compiler_LCNF_Simp_simp(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_370;
}
lean_ctor_set(x_419, 0, x_417);
if (lean_is_scalar(x_418)) {
 x_420 = lean_alloc_ctor(0, 1, 0);
} else {
 x_420 = x_418;
}
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_370);
x_421 = lean_ctor_get(x_416, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_422 = x_416;
} else {
 lean_dec_ref(x_416);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_unsigned_to_nat(1u);
x_425 = lean_nat_sub(x_412, x_424);
lean_dec(x_412);
if (lean_is_scalar(x_413)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_413;
 lean_ctor_set_tag(x_426, 0);
}
lean_ctor_set(x_426, 0, x_425);
x_427 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_428 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_429 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_13, x_427, x_428, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = lean_array_get_borrowed(x_371, x_410, x_414);
x_432 = lean_ctor_get(x_431, 0);
x_433 = lean_ctor_get(x_430, 0);
lean_inc(x_433);
lean_inc(x_432);
x_434 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_432, x_433, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; 
lean_dec_ref(x_434);
lean_inc(x_6);
x_435 = l_Lean_Compiler_LCNF_Simp_simp(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
x_437 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_13, x_410, x_6);
lean_dec(x_6);
lean_dec_ref(x_410);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_438 = x_437;
} else {
 lean_dec_ref(x_437);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_376;
}
lean_ctor_set(x_439, 0, x_430);
lean_ctor_set(x_439, 1, x_436);
if (lean_is_scalar(x_370)) {
 x_440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_440 = x_370;
}
lean_ctor_set(x_440, 0, x_439);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 1, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_440);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_436);
lean_dec(x_430);
lean_dec(x_376);
lean_dec(x_370);
x_442 = lean_ctor_get(x_437, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_443 = x_437;
} else {
 lean_dec_ref(x_437);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_430);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_370);
lean_dec(x_6);
x_445 = lean_ctor_get(x_435, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_446 = x_435;
} else {
 lean_dec_ref(x_435);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_430);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_370);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_448 = lean_ctor_get(x_434, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 x_449 = x_434;
} else {
 lean_dec_ref(x_434);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_448);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec(x_376);
lean_dec(x_370);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_451 = lean_ctor_get(x_429, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 x_452 = x_429;
} else {
 lean_dec_ref(x_429);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_376);
lean_dec(x_369);
x_454 = lean_ctor_get(x_374, 0);
lean_inc_ref(x_454);
lean_dec_ref(x_374);
x_455 = l_Lean_Compiler_LCNF_Simp_simp(x_454, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_370;
}
lean_ctor_set(x_458, 0, x_456);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(0, 1, 0);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_458);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_370);
x_460 = lean_ctor_get(x_455, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_461 = x_455;
} else {
 lean_dec_ref(x_455);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_460);
return x_462;
}
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_463 = lean_ctor_get(x_379, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_464 = x_379;
} else {
 lean_dec_ref(x_379);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 1, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_463);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_376);
lean_dec(x_374);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_466 = lean_ctor_get(x_378, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_467 = x_378;
} else {
 lean_dec_ref(x_378);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 1, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_466);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_367);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_469 = lean_box(0);
if (lean_is_scalar(x_368)) {
 x_470 = lean_alloc_ctor(0, 1, 0);
} else {
 x_470 = x_368;
}
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_366, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_472 = x_366;
} else {
 lean_dec_ref(x_366);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_471);
return x_473;
}
}
}
else
{
lean_object* x_474; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_474 = l_Lean_Compiler_LCNF_mkReturnErased(x_13, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_474) == 0)
{
uint8_t x_475; 
x_475 = !lean_is_exclusive(x_474);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_ctor_get(x_474, 0);
x_477 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_474, 0, x_477);
return x_474;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_474, 0);
lean_inc(x_478);
lean_dec(x_474);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_478);
x_480 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_480, 0, x_479);
return x_480;
}
}
else
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_474);
if (x_481 == 0)
{
return x_474;
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_474, 0);
lean_inc(x_482);
lean_dec(x_474);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_482);
return x_483;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget_borrowed(x_5, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_68; lean_object* x_69; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
x_33 = lean_ctor_get(x_17, 2);
x_34 = 0;
x_64 = lean_nat_dec_eq(x_2, x_3);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_array_get_size(x_32);
x_73 = lean_nat_dec_lt(x_71, x_72);
if (x_73 == 0)
{
x_68 = x_64;
x_69 = lean_box(0);
goto block_70;
}
else
{
if (x_73 == 0)
{
x_68 = x_64;
x_69 = lean_box(0);
goto block_70;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_72);
x_76 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_32, x_74, x_75, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
x_68 = x_78;
x_69 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_79; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
block_63:
{
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_32);
lean_inc(x_31);
lean_inc(x_1);
x_37 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_31, x_32, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_33);
x_39 = l_Lean_Compiler_LCNF_Simp_simp(x_33, x_6, x_7, x_38, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc_ref(x_17);
x_41 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_40);
x_18 = x_41;
x_19 = lean_box(0);
goto block_30;
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_33);
x_48 = l_Lean_Compiler_LCNF_Code_inferType(x_34, x_33, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_34, x_33, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_52, 0, x_49);
lean_inc_ref(x_17);
x_53 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_52);
x_18 = x_53;
x_19 = lean_box(0);
goto block_30;
}
else
{
uint8_t x_54; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
block_67:
{
if (x_64 == 0)
{
x_35 = lean_box(0);
x_36 = x_64;
goto block_63;
}
else
{
x_35 = lean_box(0);
x_36 = x_65;
goto block_63;
}
}
block_70:
{
if (lean_obj_tag(x_33) == 6)
{
x_65 = x_68;
x_66 = lean_box(0);
goto block_67;
}
else
{
if (x_64 == 0)
{
x_35 = lean_box(0);
x_36 = x_68;
goto block_63;
}
else
{
x_65 = x_68;
x_66 = lean_box(0);
goto block_67;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_17, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_82);
x_83 = l_Lean_Compiler_LCNF_Simp_simp(x_82, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc_ref(x_17);
x_85 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_84);
x_18 = x_85;
x_19 = lean_box(0);
goto block_30;
}
else
{
uint8_t x_86; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
block_30:
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_17);
x_21 = lean_ptr_addr(x_18);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
x_25 = lean_array_fset(x_5, x_4, x_18);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_4 = x_28;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; 
x_106 = lean_ctor_get(x_7, 0);
x_107 = lean_ctor_get(x_7, 1);
x_108 = lean_ctor_get(x_7, 2);
x_109 = lean_ctor_get(x_7, 3);
x_110 = lean_ctor_get(x_7, 4);
x_111 = lean_ctor_get(x_7, 5);
x_112 = lean_ctor_get(x_7, 6);
x_113 = lean_ctor_get(x_7, 7);
x_114 = lean_ctor_get(x_7, 8);
x_115 = lean_ctor_get(x_7, 9);
x_116 = lean_ctor_get(x_7, 10);
x_117 = lean_ctor_get(x_7, 11);
x_118 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_119 = lean_ctor_get(x_7, 12);
x_120 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_121 = lean_ctor_get(x_7, 13);
x_122 = lean_nat_dec_eq(x_109, x_110);
if (x_122 == 0)
{
uint8_t x_123; 
lean_inc_ref(x_121);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc_ref(x_107);
lean_inc_ref(x_106);
x_123 = !lean_is_exclusive(x_7);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_7, 13);
lean_dec(x_124);
x_125 = lean_ctor_get(x_7, 12);
lean_dec(x_125);
x_126 = lean_ctor_get(x_7, 11);
lean_dec(x_126);
x_127 = lean_ctor_get(x_7, 10);
lean_dec(x_127);
x_128 = lean_ctor_get(x_7, 9);
lean_dec(x_128);
x_129 = lean_ctor_get(x_7, 8);
lean_dec(x_129);
x_130 = lean_ctor_get(x_7, 7);
lean_dec(x_130);
x_131 = lean_ctor_get(x_7, 6);
lean_dec(x_131);
x_132 = lean_ctor_get(x_7, 5);
lean_dec(x_132);
x_133 = lean_ctor_get(x_7, 4);
lean_dec(x_133);
x_134 = lean_ctor_get(x_7, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_7, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_7, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_7, 0);
lean_dec(x_137);
x_138 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_190; lean_object* x_191; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_109, x_190);
lean_inc(x_110);
lean_ctor_set(x_7, 3, x_191);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_351; 
lean_free_object(x_138);
lean_dec(x_110);
lean_dec(x_109);
x_192 = lean_ctor_get(x_1, 0);
x_193 = lean_ctor_get(x_1, 1);
x_335 = 0;
lean_inc_ref(x_192);
x_351 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_335, x_122, x_192, x_3, x_6);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_386; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
lean_dec_ref(x_351);
lean_inc(x_352);
lean_inc_ref(x_192);
x_386 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_335, x_192, x_352);
if (x_386 == 0)
{
goto block_385;
}
else
{
if (x_122 == 0)
{
x_353 = x_2;
x_354 = x_3;
x_355 = x_4;
x_356 = x_5;
x_357 = x_6;
x_358 = x_7;
x_359 = x_8;
x_360 = lean_box(0);
goto block_380;
}
else
{
goto block_385;
}
}
block_380:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_352, 2);
x_362 = lean_ctor_get(x_352, 3);
lean_inc(x_359);
lean_inc_ref(x_358);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc_ref(x_355);
lean_inc(x_362);
x_363 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_362, x_353, x_355, x_356, x_357, x_358, x_359);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec_ref(x_363);
if (lean_obj_tag(x_364) == 1)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_366 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_354);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
lean_dec_ref(x_366);
x_367 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_335, x_352, x_365, x_357);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = lean_ctor_get(x_368, 2);
lean_inc_ref(x_369);
x_370 = lean_ctor_get(x_368, 3);
lean_inc(x_370);
x_336 = x_368;
x_337 = x_369;
x_338 = x_370;
x_339 = x_353;
x_340 = x_354;
x_341 = x_355;
x_342 = x_356;
x_343 = x_357;
x_344 = x_358;
x_345 = x_359;
x_346 = lean_box(0);
goto block_350;
}
else
{
uint8_t x_371; 
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec_ref(x_1);
x_371 = !lean_is_exclusive(x_367);
if (x_371 == 0)
{
return x_367;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_367, 0);
lean_inc(x_372);
lean_dec(x_367);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_365);
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_1);
x_374 = !lean_is_exclusive(x_366);
if (x_374 == 0)
{
return x_366;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_366, 0);
lean_inc(x_375);
lean_dec(x_366);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
}
}
else
{
lean_dec(x_364);
lean_inc(x_362);
lean_inc_ref(x_361);
x_336 = x_352;
x_337 = x_361;
x_338 = x_362;
x_339 = x_353;
x_340 = x_354;
x_341 = x_355;
x_342 = x_356;
x_343 = x_357;
x_344 = x_358;
x_345 = x_359;
x_346 = lean_box(0);
goto block_350;
}
}
else
{
uint8_t x_377; 
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec_ref(x_353);
lean_dec(x_352);
lean_dec_ref(x_1);
x_377 = !lean_is_exclusive(x_363);
if (x_377 == 0)
{
return x_363;
}
else
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_ctor_get(x_363, 0);
lean_inc(x_378);
lean_dec(x_363);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_378);
return x_379;
}
}
}
block_385:
{
lean_object* x_381; 
x_381 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_381) == 0)
{
lean_dec_ref(x_381);
x_353 = x_2;
x_354 = x_3;
x_355 = x_4;
x_356 = x_5;
x_357 = x_6;
x_358 = x_7;
x_359 = x_8;
x_360 = lean_box(0);
goto block_380;
}
else
{
uint8_t x_382; 
lean_dec(x_352);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
return x_381;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
}
}
else
{
uint8_t x_387; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_387 = !lean_is_exclusive(x_351);
if (x_387 == 0)
{
return x_351;
}
else
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_351, 0);
lean_inc(x_388);
lean_dec(x_351);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_388);
return x_389;
}
}
block_334:
{
if (x_203 == 0)
{
lean_object* x_204; 
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_196);
x_204 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_196, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
if (lean_obj_tag(x_205) == 1)
{
lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_196);
lean_inc_ref(x_193);
lean_dec_ref(x_1);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_199);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
lean_dec_ref(x_207);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_202);
lean_inc(x_199);
lean_inc_ref(x_198);
x_208 = l_Lean_Compiler_LCNF_Simp_simp(x_193, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_206, x_209, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
lean_dec(x_201);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_197);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_206);
return x_210;
}
else
{
lean_dec(x_206);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
return x_208;
}
}
else
{
uint8_t x_211; 
lean_dec(x_206);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_211 = !lean_is_exclusive(x_207);
if (x_211 == 0)
{
return x_207;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
lean_dec(x_207);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; 
lean_dec(x_205);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_196);
x_214 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_196, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
if (lean_obj_tag(x_215) == 1)
{
uint8_t x_216; 
lean_dec_ref(x_196);
lean_inc_ref(x_193);
x_216 = !lean_is_exclusive(x_1);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_1, 1);
lean_dec(x_217);
x_218 = lean_ctor_get(x_1, 0);
lean_dec(x_218);
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
lean_dec_ref(x_215);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_219);
x_2 = x_198;
x_3 = x_199;
x_4 = x_202;
x_5 = x_197;
x_6 = x_194;
x_7 = x_195;
x_8 = x_201;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_1);
x_221 = lean_ctor_get(x_215, 0);
lean_inc(x_221);
lean_dec_ref(x_215);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_193);
x_1 = x_222;
x_2 = x_198;
x_3 = x_199;
x_4 = x_202;
x_5 = x_197;
x_6 = x_194;
x_7 = x_195;
x_8 = x_201;
goto _start;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_215);
x_224 = lean_ctor_get(x_196, 0);
x_225 = lean_ctor_get(x_196, 3);
x_226 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
if (lean_obj_tag(x_227) == 1)
{
lean_object* x_228; lean_object* x_229; 
lean_inc_ref(x_193);
lean_dec_ref(x_1);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
lean_inc(x_224);
x_229 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_224, x_228, x_199, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec_ref(x_229);
x_230 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec_ref(x_196);
if (lean_obj_tag(x_230) == 0)
{
lean_dec_ref(x_230);
x_1 = x_193;
x_2 = x_198;
x_3 = x_199;
x_4 = x_202;
x_5 = x_197;
x_6 = x_194;
x_7 = x_195;
x_8 = x_201;
goto _start;
}
else
{
uint8_t x_232; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_232 = !lean_is_exclusive(x_230);
if (x_232 == 0)
{
return x_230;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_235 = !lean_is_exclusive(x_229);
if (x_235 == 0)
{
return x_229;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_229, 0);
lean_inc(x_236);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; 
lean_dec(x_227);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_202);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc_ref(x_193);
lean_inc_ref(x_196);
x_238 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_196, x_193, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
if (lean_obj_tag(x_239) == 1)
{
lean_object* x_240; lean_object* x_241; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec(x_194);
lean_dec(x_199);
lean_dec_ref(x_196);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_241, 0);
lean_dec(x_243);
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
else
{
lean_object* x_244; 
lean_dec(x_241);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_240);
return x_244;
}
}
else
{
uint8_t x_245; 
lean_dec(x_240);
x_245 = !lean_is_exclusive(x_241);
if (x_245 == 0)
{
return x_241;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_241, 0);
lean_inc(x_246);
lean_dec(x_241);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
}
}
else
{
lean_object* x_248; 
lean_dec(x_239);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_202);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc(x_225);
x_248 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_225, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
if (lean_obj_tag(x_249) == 1)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_inc_ref(x_193);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_224);
x_253 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_224, x_252, x_199, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec_ref(x_253);
x_254 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec_ref(x_196);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; 
lean_dec_ref(x_254);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_202);
lean_inc(x_199);
lean_inc_ref(x_198);
x_255 = l_Lean_Compiler_LCNF_Simp_simp(x_193, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_251, x_256, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
lean_dec(x_201);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_197);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_251);
return x_257;
}
else
{
lean_dec(x_251);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
return x_255;
}
}
else
{
uint8_t x_258; 
lean_dec(x_251);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
return x_254;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_254, 0);
lean_inc(x_259);
lean_dec(x_254);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_251);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_261 = !lean_is_exclusive(x_253);
if (x_261 == 0)
{
return x_253;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_253, 0);
lean_inc(x_262);
lean_dec(x_253);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; 
lean_dec(x_249);
lean_inc(x_201);
lean_inc_ref(x_195);
lean_inc(x_194);
lean_inc_ref(x_197);
lean_inc_ref(x_202);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc_ref(x_193);
x_264 = l_Lean_Compiler_LCNF_Simp_simp(x_193, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec_ref(x_264);
x_266 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_224, x_199);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_unbox(x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec_ref(x_1);
x_269 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec(x_194);
lean_dec(x_199);
lean_dec_ref(x_196);
if (lean_obj_tag(x_269) == 0)
{
uint8_t x_270; 
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_269, 0);
lean_dec(x_271);
lean_ctor_set(x_269, 0, x_265);
return x_269;
}
else
{
lean_object* x_272; 
lean_dec(x_269);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_265);
return x_272;
}
}
else
{
uint8_t x_273; 
lean_dec(x_265);
x_273 = !lean_is_exclusive(x_269);
if (x_273 == 0)
{
return x_269;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_269, 0);
lean_inc(x_274);
lean_dec(x_269);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; 
lean_inc_ref(x_196);
x_276 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_196, x_198, x_199, x_202, x_197, x_194, x_195, x_201);
lean_dec(x_201);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_197);
lean_dec_ref(x_202);
lean_dec(x_199);
lean_dec_ref(x_198);
if (lean_obj_tag(x_276) == 0)
{
size_t x_277; size_t x_278; uint8_t x_279; 
lean_dec_ref(x_276);
x_277 = lean_ptr_addr(x_193);
x_278 = lean_ptr_addr(x_265);
x_279 = lean_usize_dec_eq(x_277, x_278);
if (x_279 == 0)
{
x_98 = x_265;
x_99 = x_196;
x_100 = lean_box(0);
x_101 = x_279;
goto block_105;
}
else
{
size_t x_280; size_t x_281; uint8_t x_282; 
x_280 = lean_ptr_addr(x_192);
x_281 = lean_ptr_addr(x_196);
x_282 = lean_usize_dec_eq(x_280, x_281);
x_98 = x_265;
x_99 = x_196;
x_100 = lean_box(0);
x_101 = x_282;
goto block_105;
}
}
else
{
uint8_t x_283; 
lean_dec(x_265);
lean_dec_ref(x_196);
lean_dec_ref(x_1);
x_283 = !lean_is_exclusive(x_276);
if (x_283 == 0)
{
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_276, 0);
lean_inc(x_284);
lean_dec(x_276);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
}
else
{
uint8_t x_286; 
lean_dec(x_265);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_286 = !lean_is_exclusive(x_266);
if (x_286 == 0)
{
return x_266;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_266, 0);
lean_inc(x_287);
lean_dec(x_266);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
return x_264;
}
}
}
else
{
uint8_t x_289; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_289 = !lean_is_exclusive(x_248);
if (x_289 == 0)
{
return x_248;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_248, 0);
lean_inc(x_290);
lean_dec(x_248);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_238);
if (x_292 == 0)
{
return x_238;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_238, 0);
lean_inc(x_293);
lean_dec(x_238);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_295 = !lean_is_exclusive(x_226);
if (x_295 == 0)
{
return x_226;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_226, 0);
lean_inc(x_296);
lean_dec(x_226);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
}
}
else
{
uint8_t x_298; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_298 = !lean_is_exclusive(x_214);
if (x_298 == 0)
{
return x_214;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_214, 0);
lean_inc(x_299);
lean_dec(x_214);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
}
else
{
uint8_t x_301; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_1);
x_301 = !lean_is_exclusive(x_204);
if (x_301 == 0)
{
return x_204;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_204, 0);
lean_inc(x_302);
lean_dec(x_204);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
}
else
{
lean_object* x_304; uint8_t x_305; 
lean_inc_ref(x_193);
lean_dec_ref(x_1);
x_304 = lean_st_ref_take(x_199);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_196, 0);
x_307 = lean_ctor_get(x_304, 0);
x_308 = lean_box(0);
lean_inc(x_306);
x_309 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_307, x_306, x_308);
lean_ctor_set(x_304, 0, x_309);
x_310 = lean_st_ref_set(x_199, x_304);
x_311 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec_ref(x_196);
if (lean_obj_tag(x_311) == 0)
{
lean_dec_ref(x_311);
x_1 = x_193;
x_2 = x_198;
x_3 = x_199;
x_4 = x_202;
x_5 = x_197;
x_6 = x_194;
x_7 = x_195;
x_8 = x_201;
goto _start;
}
else
{
uint8_t x_313; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_313 = !lean_is_exclusive(x_311);
if (x_313 == 0)
{
return x_311;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_316 = lean_ctor_get(x_196, 0);
x_317 = lean_ctor_get(x_304, 0);
x_318 = lean_ctor_get(x_304, 1);
x_319 = lean_ctor_get(x_304, 2);
x_320 = lean_ctor_get(x_304, 3);
x_321 = lean_ctor_get_uint8(x_304, sizeof(void*)*7);
x_322 = lean_ctor_get(x_304, 4);
x_323 = lean_ctor_get(x_304, 5);
x_324 = lean_ctor_get(x_304, 6);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_304);
x_325 = lean_box(0);
lean_inc(x_316);
x_326 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_317, x_316, x_325);
x_327 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_318);
lean_ctor_set(x_327, 2, x_319);
lean_ctor_set(x_327, 3, x_320);
lean_ctor_set(x_327, 4, x_322);
lean_ctor_set(x_327, 5, x_323);
lean_ctor_set(x_327, 6, x_324);
lean_ctor_set_uint8(x_327, sizeof(void*)*7, x_321);
x_328 = lean_st_ref_set(x_199, x_327);
x_329 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_196, x_199, x_194);
lean_dec_ref(x_196);
if (lean_obj_tag(x_329) == 0)
{
lean_dec_ref(x_329);
x_1 = x_193;
x_2 = x_198;
x_3 = x_199;
x_4 = x_202;
x_5 = x_197;
x_6 = x_194;
x_7 = x_195;
x_8 = x_201;
goto _start;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 1, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_331);
return x_333;
}
}
}
}
block_350:
{
uint8_t x_347; 
x_347 = l_Lean_Expr_isErased(x_337);
lean_dec_ref(x_337);
if (x_347 == 0)
{
lean_dec(x_338);
x_194 = x_343;
x_195 = x_344;
x_196 = x_336;
x_197 = x_342;
x_198 = x_339;
x_199 = x_340;
x_200 = lean_box(0);
x_201 = x_345;
x_202 = x_341;
x_203 = x_122;
goto block_334;
}
else
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_box(1);
x_349 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_335, x_338, x_348);
if (x_349 == 0)
{
x_194 = x_343;
x_195 = x_344;
x_196 = x_336;
x_197 = x_342;
x_198 = x_339;
x_199 = x_340;
x_200 = lean_box(0);
x_201 = x_345;
x_202 = x_341;
x_203 = x_347;
goto block_334;
}
else
{
x_194 = x_343;
x_195 = x_344;
x_196 = x_336;
x_197 = x_342;
x_198 = x_339;
x_199 = x_340;
x_200 = lean_box(0);
x_201 = x_345;
x_202 = x_341;
x_203 = x_122;
goto block_334;
}
}
}
}
case 3:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; 
lean_free_object(x_138);
lean_dec(x_110);
lean_dec(x_109);
x_390 = lean_ctor_get(x_1, 0);
x_391 = lean_ctor_get(x_1, 1);
x_392 = lean_st_ref_get(x_3);
x_393 = lean_ctor_get(x_392, 0);
lean_inc_ref(x_393);
lean_dec(x_392);
x_394 = 0;
lean_inc(x_390);
x_395 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_393, x_390, x_122);
lean_dec_ref(x_393);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec_ref(x_395);
lean_inc_ref(x_391);
x_397 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_394, x_122, x_391, x_3);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_410; lean_object* x_416; lean_object* x_421; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_398);
x_421 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_396, x_398, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
if (lean_obj_tag(x_422) == 1)
{
lean_object* x_423; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_396);
lean_dec_ref(x_1);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
x_1 = x_423;
goto _start;
}
else
{
lean_object* x_425; 
lean_dec(x_422);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_396);
x_425 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_396, x_3);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
lean_dec_ref(x_425);
x_426 = lean_unsigned_to_nat(0u);
x_427 = lean_array_get_size(x_398);
x_428 = lean_nat_dec_lt(x_426, x_427);
if (x_428 == 0)
{
lean_dec(x_3);
x_410 = lean_box(0);
goto block_415;
}
else
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_box(0);
x_430 = lean_nat_dec_le(x_427, x_427);
if (x_430 == 0)
{
if (x_428 == 0)
{
lean_dec(x_3);
x_410 = lean_box(0);
goto block_415;
}
else
{
size_t x_431; size_t x_432; lean_object* x_433; 
x_431 = 0;
x_432 = lean_usize_of_nat(x_427);
x_433 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_398, x_431, x_432, x_429, x_3);
lean_dec(x_3);
x_416 = x_433;
goto block_420;
}
}
else
{
size_t x_434; size_t x_435; lean_object* x_436; 
x_434 = 0;
x_435 = lean_usize_of_nat(x_427);
x_436 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_398, x_434, x_435, x_429, x_3);
lean_dec(x_3);
x_416 = x_436;
goto block_420;
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_3);
lean_dec_ref(x_1);
x_437 = !lean_is_exclusive(x_425);
if (x_437 == 0)
{
return x_425;
}
else
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_425, 0);
lean_inc(x_438);
lean_dec(x_425);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_438);
return x_439;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_396);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_440 = !lean_is_exclusive(x_421);
if (x_440 == 0)
{
return x_421;
}
else
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_421, 0);
lean_inc(x_441);
lean_dec(x_421);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_441);
return x_442;
}
}
block_409:
{
if (x_401 == 0)
{
uint8_t x_402; 
x_402 = !lean_is_exclusive(x_1);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_1, 1);
lean_dec(x_403);
x_404 = lean_ctor_get(x_1, 0);
lean_dec(x_404);
lean_ctor_set(x_1, 1, x_398);
lean_ctor_set(x_1, 0, x_396);
if (lean_is_scalar(x_399)) {
 x_405 = lean_alloc_ctor(0, 1, 0);
} else {
 x_405 = x_399;
}
lean_ctor_set(x_405, 0, x_1);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_1);
x_406 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_406, 0, x_396);
lean_ctor_set(x_406, 1, x_398);
if (lean_is_scalar(x_399)) {
 x_407 = lean_alloc_ctor(0, 1, 0);
} else {
 x_407 = x_399;
}
lean_ctor_set(x_407, 0, x_406);
return x_407;
}
}
else
{
lean_object* x_408; 
lean_dec(x_398);
lean_dec(x_396);
if (lean_is_scalar(x_399)) {
 x_408 = lean_alloc_ctor(0, 1, 0);
} else {
 x_408 = x_399;
}
lean_ctor_set(x_408, 0, x_1);
return x_408;
}
}
block_415:
{
uint8_t x_411; 
x_411 = l_Lean_instBEqFVarId_beq(x_390, x_396);
if (x_411 == 0)
{
x_400 = lean_box(0);
x_401 = x_411;
goto block_409;
}
else
{
size_t x_412; size_t x_413; uint8_t x_414; 
x_412 = lean_ptr_addr(x_391);
x_413 = lean_ptr_addr(x_398);
x_414 = lean_usize_dec_eq(x_412, x_413);
x_400 = lean_box(0);
x_401 = x_414;
goto block_409;
}
}
block_420:
{
if (lean_obj_tag(x_416) == 0)
{
lean_dec_ref(x_416);
x_410 = lean_box(0);
goto block_415;
}
else
{
uint8_t x_417; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_396);
lean_dec_ref(x_1);
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
return x_416;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_416, 0);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_419, 0, x_418);
return x_419;
}
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_396);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_443 = !lean_is_exclusive(x_397);
if (x_443 == 0)
{
return x_397;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_397, 0);
lean_inc(x_444);
lean_dec(x_397);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
return x_445;
}
}
}
else
{
lean_object* x_446; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_446 = l_Lean_Compiler_LCNF_mkReturnErased(x_394, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_446;
}
}
case 4:
{
lean_object* x_447; lean_object* x_448; 
lean_free_object(x_138);
x_447 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_447);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_447);
x_448 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_447, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_448) == 0)
{
uint8_t x_449; 
x_449 = !lean_is_exclusive(x_448);
if (x_449 == 0)
{
lean_object* x_450; 
x_450 = lean_ctor_get(x_448, 0);
if (lean_obj_tag(x_450) == 1)
{
lean_object* x_451; 
lean_dec_ref(x_447);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
lean_ctor_set(x_448, 0, x_451);
return x_448;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; 
lean_dec(x_450);
x_452 = lean_ctor_get(x_447, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_447, 1);
lean_inc_ref(x_453);
x_454 = lean_ctor_get(x_447, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_447, 3);
lean_inc_ref(x_455);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 lean_ctor_release(x_447, 2);
 lean_ctor_release(x_447, 3);
 x_456 = x_447;
} else {
 lean_dec_ref(x_447);
 x_456 = lean_box(0);
}
x_457 = lean_st_ref_get(x_3);
x_458 = lean_ctor_get(x_457, 0);
lean_inc_ref(x_458);
lean_dec(x_457);
x_459 = 0;
lean_inc(x_454);
x_460 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_458, x_454, x_122);
lean_dec_ref(x_458);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 x_462 = x_460;
} else {
 lean_dec_ref(x_460);
 x_462 = lean_box(0);
}
x_463 = lean_st_ref_get(x_3);
x_464 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_455);
lean_inc(x_461);
x_465 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_461, x_109, x_110, x_464, x_455, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_468 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_466, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_485; lean_object* x_486; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_508; lean_object* x_513; uint8_t x_514; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_540; uint8_t x_541; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_470 = x_468;
} else {
 lean_dec_ref(x_468);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_463, 0);
lean_inc_ref(x_471);
lean_dec(x_463);
lean_inc_ref(x_453);
x_472 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_459, x_471, x_122, x_453);
lean_dec_ref(x_471);
x_540 = lean_array_get_size(x_469);
x_541 = lean_nat_dec_eq(x_540, x_190);
if (x_541 == 0)
{
lean_free_object(x_448);
x_518 = x_3;
x_519 = x_5;
x_520 = x_6;
x_521 = x_7;
x_522 = x_8;
x_523 = lean_box(0);
goto block_539;
}
else
{
lean_object* x_542; 
x_542 = lean_array_fget_borrowed(x_469, x_464);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_554; lean_object* x_559; lean_object* x_560; uint8_t x_571; lean_object* x_572; uint8_t x_574; 
lean_free_object(x_448);
x_543 = lean_ctor_get(x_542, 1);
x_544 = lean_ctor_get(x_542, 2);
x_559 = lean_array_get_size(x_543);
x_574 = lean_nat_dec_lt(x_464, x_559);
if (x_574 == 0)
{
x_571 = x_122;
x_572 = lean_box(0);
goto block_573;
}
else
{
if (x_574 == 0)
{
x_571 = x_122;
x_572 = lean_box(0);
goto block_573;
}
else
{
size_t x_575; size_t x_576; lean_object* x_577; 
x_575 = 0;
x_576 = lean_usize_of_nat(x_559);
x_577 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_543, x_575, x_576, x_3);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; uint8_t x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
x_579 = lean_unbox(x_578);
lean_dec(x_578);
x_571 = x_579;
x_572 = lean_box(0);
goto block_573;
}
else
{
uint8_t x_580; 
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_580 = !lean_is_exclusive(x_577);
if (x_580 == 0)
{
return x_577;
}
else
{
lean_object* x_581; lean_object* x_582; 
x_581 = lean_ctor_get(x_577, 0);
lean_inc(x_581);
lean_dec(x_577);
x_582 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_582, 0, x_581);
return x_582;
}
}
}
}
block_553:
{
lean_object* x_546; 
x_546 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_546) == 0)
{
uint8_t x_547; 
x_547 = !lean_is_exclusive(x_546);
if (x_547 == 0)
{
lean_object* x_548; 
x_548 = lean_ctor_get(x_546, 0);
lean_dec(x_548);
lean_ctor_set(x_546, 0, x_544);
return x_546;
}
else
{
lean_object* x_549; 
lean_dec(x_546);
x_549 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_549, 0, x_544);
return x_549;
}
}
else
{
uint8_t x_550; 
lean_dec_ref(x_544);
x_550 = !lean_is_exclusive(x_546);
if (x_550 == 0)
{
return x_546;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_ctor_get(x_546, 0);
lean_inc(x_551);
lean_dec(x_546);
x_552 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_552, 0, x_551);
return x_552;
}
}
}
block_558:
{
if (lean_obj_tag(x_554) == 0)
{
lean_dec_ref(x_554);
x_545 = lean_box(0);
goto block_553;
}
else
{
uint8_t x_555; 
lean_dec_ref(x_544);
lean_dec(x_3);
x_555 = !lean_is_exclusive(x_554);
if (x_555 == 0)
{
return x_554;
}
else
{
lean_object* x_556; lean_object* x_557; 
x_556 = lean_ctor_get(x_554, 0);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_557, 0, x_556);
return x_557;
}
}
}
block_570:
{
uint8_t x_561; 
x_561 = lean_nat_dec_lt(x_464, x_559);
if (x_561 == 0)
{
lean_dec_ref(x_543);
lean_dec(x_6);
x_545 = lean_box(0);
goto block_553;
}
else
{
lean_object* x_562; uint8_t x_563; 
x_562 = lean_box(0);
x_563 = lean_nat_dec_le(x_559, x_559);
if (x_563 == 0)
{
if (x_561 == 0)
{
lean_dec_ref(x_543);
lean_dec(x_6);
x_545 = lean_box(0);
goto block_553;
}
else
{
size_t x_564; size_t x_565; lean_object* x_566; 
x_564 = 0;
x_565 = lean_usize_of_nat(x_559);
x_566 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_543, x_564, x_565, x_562, x_6);
lean_dec(x_6);
lean_dec_ref(x_543);
x_554 = x_566;
goto block_558;
}
}
else
{
size_t x_567; size_t x_568; lean_object* x_569; 
x_567 = 0;
x_568 = lean_usize_of_nat(x_559);
x_569 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_543, x_567, x_568, x_562, x_6);
lean_dec(x_6);
lean_dec_ref(x_543);
x_554 = x_569;
goto block_558;
}
}
}
block_573:
{
if (x_571 == 0)
{
lean_inc_ref(x_544);
lean_inc_ref(x_543);
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_560 = lean_box(0);
goto block_570;
}
else
{
if (x_122 == 0)
{
x_518 = x_3;
x_519 = x_5;
x_520 = x_6;
x_521 = x_7;
x_522 = x_8;
x_523 = lean_box(0);
goto block_539;
}
else
{
lean_inc_ref(x_544);
lean_inc_ref(x_543);
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_560 = lean_box(0);
goto block_570;
}
}
}
}
else
{
lean_object* x_583; 
lean_inc_ref(x_542);
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_583 = lean_ctor_get(x_542, 0);
lean_inc_ref(x_583);
lean_dec_ref(x_542);
lean_ctor_set(x_448, 0, x_583);
return x_448;
}
}
block_484:
{
lean_object* x_475; 
x_475 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_473);
lean_dec(x_473);
if (lean_obj_tag(x_475) == 0)
{
uint8_t x_476; 
x_476 = !lean_is_exclusive(x_475);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_475, 0);
lean_dec(x_477);
if (lean_is_scalar(x_462)) {
 x_478 = lean_alloc_ctor(6, 1, 0);
} else {
 x_478 = x_462;
 lean_ctor_set_tag(x_478, 6);
}
lean_ctor_set(x_478, 0, x_472);
lean_ctor_set(x_475, 0, x_478);
return x_475;
}
else
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_475);
if (lean_is_scalar(x_462)) {
 x_479 = lean_alloc_ctor(6, 1, 0);
} else {
 x_479 = x_462;
 lean_ctor_set_tag(x_479, 6);
}
lean_ctor_set(x_479, 0, x_472);
x_480 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_480, 0, x_479);
return x_480;
}
}
else
{
uint8_t x_481; 
lean_dec_ref(x_472);
lean_dec(x_462);
x_481 = !lean_is_exclusive(x_475);
if (x_481 == 0)
{
return x_475;
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_475, 0);
lean_inc(x_482);
lean_dec(x_475);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_482);
return x_483;
}
}
}
block_490:
{
if (lean_obj_tag(x_486) == 0)
{
lean_dec_ref(x_486);
x_473 = x_485;
x_474 = lean_box(0);
goto block_484;
}
else
{
uint8_t x_487; 
lean_dec(x_485);
lean_dec_ref(x_472);
lean_dec(x_462);
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
return x_486;
}
else
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_488);
return x_489;
}
}
}
block_507:
{
uint8_t x_498; 
x_498 = lean_nat_dec_lt(x_464, x_494);
if (x_498 == 0)
{
lean_dec(x_496);
lean_dec(x_494);
lean_dec_ref(x_493);
lean_dec_ref(x_492);
lean_dec(x_491);
lean_dec(x_469);
x_473 = x_495;
x_474 = lean_box(0);
goto block_484;
}
else
{
lean_object* x_499; uint8_t x_500; 
x_499 = lean_box(0);
x_500 = lean_nat_dec_le(x_494, x_494);
if (x_500 == 0)
{
if (x_498 == 0)
{
lean_dec(x_496);
lean_dec(x_494);
lean_dec_ref(x_493);
lean_dec_ref(x_492);
lean_dec(x_491);
lean_dec(x_469);
x_473 = x_495;
x_474 = lean_box(0);
goto block_484;
}
else
{
size_t x_501; size_t x_502; lean_object* x_503; 
x_501 = 0;
x_502 = lean_usize_of_nat(x_494);
lean_dec(x_494);
x_503 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_469, x_501, x_502, x_499, x_493, x_496, x_492, x_491);
lean_dec(x_491);
lean_dec_ref(x_492);
lean_dec(x_496);
lean_dec_ref(x_493);
lean_dec(x_469);
x_485 = x_495;
x_486 = x_503;
goto block_490;
}
}
else
{
size_t x_504; size_t x_505; lean_object* x_506; 
x_504 = 0;
x_505 = lean_usize_of_nat(x_494);
lean_dec(x_494);
x_506 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_469, x_504, x_505, x_499, x_493, x_496, x_492, x_491);
lean_dec(x_491);
lean_dec_ref(x_492);
lean_dec(x_496);
lean_dec_ref(x_493);
lean_dec(x_469);
x_485 = x_495;
x_486 = x_506;
goto block_490;
}
}
}
block_512:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
if (lean_is_scalar(x_456)) {
 x_509 = lean_alloc_ctor(0, 4, 0);
} else {
 x_509 = x_456;
}
lean_ctor_set(x_509, 0, x_452);
lean_ctor_set(x_509, 1, x_472);
lean_ctor_set(x_509, 2, x_461);
lean_ctor_set(x_509, 3, x_469);
x_510 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_510, 0, x_509);
if (lean_is_scalar(x_470)) {
 x_511 = lean_alloc_ctor(0, 1, 0);
} else {
 x_511 = x_470;
}
lean_ctor_set(x_511, 0, x_510);
return x_511;
}
block_517:
{
if (x_514 == 0)
{
lean_dec(x_467);
lean_dec(x_454);
lean_dec_ref(x_1);
x_508 = lean_box(0);
goto block_512;
}
else
{
uint8_t x_515; 
x_515 = l_Lean_instBEqFVarId_beq(x_454, x_461);
lean_dec(x_454);
if (x_515 == 0)
{
lean_dec(x_467);
lean_dec_ref(x_1);
x_508 = lean_box(0);
goto block_512;
}
else
{
lean_object* x_516; 
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_461);
lean_dec(x_456);
lean_dec(x_452);
if (lean_is_scalar(x_467)) {
 x_516 = lean_alloc_ctor(0, 1, 0);
} else {
 x_516 = x_467;
}
lean_ctor_set(x_516, 0, x_1);
return x_516;
}
}
}
block_539:
{
lean_object* x_524; uint8_t x_525; 
x_524 = lean_array_get_size(x_469);
x_525 = lean_nat_dec_lt(x_464, x_524);
if (x_525 == 0)
{
lean_dec(x_470);
lean_dec(x_467);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_491 = x_522;
x_492 = x_521;
x_493 = x_519;
x_494 = x_524;
x_495 = x_518;
x_496 = x_520;
x_497 = lean_box(0);
goto block_507;
}
else
{
if (x_525 == 0)
{
lean_dec(x_470);
lean_dec(x_467);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_491 = x_522;
x_492 = x_521;
x_493 = x_519;
x_494 = x_524;
x_495 = x_518;
x_496 = x_520;
x_497 = lean_box(0);
goto block_507;
}
else
{
size_t x_526; size_t x_527; uint8_t x_528; 
x_526 = 0;
x_527 = lean_usize_of_nat(x_524);
x_528 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_109, x_110, x_469, x_526, x_527);
lean_dec(x_110);
lean_dec(x_109);
if (x_528 == 0)
{
lean_dec(x_470);
lean_dec(x_467);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_1);
x_491 = x_522;
x_492 = x_521;
x_493 = x_519;
x_494 = x_524;
x_495 = x_518;
x_496 = x_520;
x_497 = lean_box(0);
goto block_507;
}
else
{
if (x_122 == 0)
{
lean_object* x_529; 
lean_dec(x_522);
lean_dec_ref(x_521);
lean_dec(x_520);
lean_dec_ref(x_519);
lean_dec(x_462);
lean_inc(x_461);
x_529 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_461, x_518);
lean_dec(x_518);
if (lean_obj_tag(x_529) == 0)
{
size_t x_530; size_t x_531; uint8_t x_532; 
lean_dec_ref(x_529);
x_530 = lean_ptr_addr(x_455);
lean_dec_ref(x_455);
x_531 = lean_ptr_addr(x_469);
x_532 = lean_usize_dec_eq(x_530, x_531);
if (x_532 == 0)
{
lean_dec_ref(x_453);
x_513 = lean_box(0);
x_514 = x_532;
goto block_517;
}
else
{
size_t x_533; size_t x_534; uint8_t x_535; 
x_533 = lean_ptr_addr(x_453);
lean_dec_ref(x_453);
x_534 = lean_ptr_addr(x_472);
x_535 = lean_usize_dec_eq(x_533, x_534);
x_513 = lean_box(0);
x_514 = x_535;
goto block_517;
}
}
else
{
uint8_t x_536; 
lean_dec_ref(x_472);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_1);
x_536 = !lean_is_exclusive(x_529);
if (x_536 == 0)
{
return x_529;
}
else
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_529, 0);
lean_inc(x_537);
lean_dec(x_529);
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_537);
return x_538;
}
}
}
else
{
lean_dec(x_470);
lean_dec(x_467);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_1);
x_491 = x_522;
x_492 = x_521;
x_493 = x_519;
x_494 = x_524;
x_495 = x_518;
x_496 = x_520;
x_497 = lean_box(0);
goto block_507;
}
}
}
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_467);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_free_object(x_448);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_584 = !lean_is_exclusive(x_468);
if (x_584 == 0)
{
return x_468;
}
else
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_468, 0);
lean_inc(x_585);
lean_dec(x_468);
x_586 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_586, 0, x_585);
return x_586;
}
}
}
else
{
uint8_t x_587; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_free_object(x_448);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_587 = !lean_is_exclusive(x_465);
if (x_587 == 0)
{
return x_465;
}
else
{
lean_object* x_588; lean_object* x_589; 
x_588 = lean_ctor_get(x_465, 0);
lean_inc(x_588);
lean_dec(x_465);
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_588);
return x_589;
}
}
}
else
{
lean_object* x_590; 
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_free_object(x_448);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_590 = l_Lean_Compiler_LCNF_mkReturnErased(x_459, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_590;
}
}
}
else
{
lean_object* x_591; 
x_591 = lean_ctor_get(x_448, 0);
lean_inc(x_591);
lean_dec(x_448);
if (lean_obj_tag(x_591) == 1)
{
lean_object* x_592; lean_object* x_593; 
lean_dec_ref(x_447);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
lean_dec_ref(x_591);
x_593 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_593, 0, x_592);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; lean_object* x_602; 
lean_dec(x_591);
x_594 = lean_ctor_get(x_447, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_447, 1);
lean_inc_ref(x_595);
x_596 = lean_ctor_get(x_447, 2);
lean_inc(x_596);
x_597 = lean_ctor_get(x_447, 3);
lean_inc_ref(x_597);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 lean_ctor_release(x_447, 2);
 lean_ctor_release(x_447, 3);
 x_598 = x_447;
} else {
 lean_dec_ref(x_447);
 x_598 = lean_box(0);
}
x_599 = lean_st_ref_get(x_3);
x_600 = lean_ctor_get(x_599, 0);
lean_inc_ref(x_600);
lean_dec(x_599);
x_601 = 0;
lean_inc(x_596);
x_602 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_600, x_596, x_122);
lean_dec_ref(x_600);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
x_605 = lean_st_ref_get(x_3);
x_606 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_597);
lean_inc(x_603);
x_607 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_603, x_109, x_110, x_606, x_597, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_609 = x_607;
} else {
 lean_dec_ref(x_607);
 x_609 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_610 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_608, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_625; lean_object* x_626; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_648; lean_object* x_653; uint8_t x_654; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_680; uint8_t x_681; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_612 = x_610;
} else {
 lean_dec_ref(x_610);
 x_612 = lean_box(0);
}
x_613 = lean_ctor_get(x_605, 0);
lean_inc_ref(x_613);
lean_dec(x_605);
lean_inc_ref(x_595);
x_614 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_601, x_613, x_122, x_595);
lean_dec_ref(x_613);
x_680 = lean_array_get_size(x_611);
x_681 = lean_nat_dec_eq(x_680, x_190);
if (x_681 == 0)
{
x_658 = x_3;
x_659 = x_5;
x_660 = x_6;
x_661 = x_7;
x_662 = x_8;
x_663 = lean_box(0);
goto block_679;
}
else
{
lean_object* x_682; 
x_682 = lean_array_fget_borrowed(x_611, x_606);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_693; lean_object* x_698; lean_object* x_699; uint8_t x_710; lean_object* x_711; uint8_t x_713; 
x_683 = lean_ctor_get(x_682, 1);
x_684 = lean_ctor_get(x_682, 2);
x_698 = lean_array_get_size(x_683);
x_713 = lean_nat_dec_lt(x_606, x_698);
if (x_713 == 0)
{
x_710 = x_122;
x_711 = lean_box(0);
goto block_712;
}
else
{
if (x_713 == 0)
{
x_710 = x_122;
x_711 = lean_box(0);
goto block_712;
}
else
{
size_t x_714; size_t x_715; lean_object* x_716; 
x_714 = 0;
x_715 = lean_usize_of_nat(x_698);
x_716 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_683, x_714, x_715, x_3);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; uint8_t x_718; 
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
lean_dec_ref(x_716);
x_718 = lean_unbox(x_717);
lean_dec(x_717);
x_710 = x_718;
x_711 = lean_box(0);
goto block_712;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_719 = lean_ctor_get(x_716, 0);
lean_inc(x_719);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 x_720 = x_716;
} else {
 lean_dec_ref(x_716);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 1, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_719);
return x_721;
}
}
}
block_692:
{
lean_object* x_686; 
x_686 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; 
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_687 = x_686;
} else {
 lean_dec_ref(x_686);
 x_687 = lean_box(0);
}
if (lean_is_scalar(x_687)) {
 x_688 = lean_alloc_ctor(0, 1, 0);
} else {
 x_688 = x_687;
}
lean_ctor_set(x_688, 0, x_684);
return x_688;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec_ref(x_684);
x_689 = lean_ctor_get(x_686, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 x_690 = x_686;
} else {
 lean_dec_ref(x_686);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(1, 1, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_689);
return x_691;
}
}
block_697:
{
if (lean_obj_tag(x_693) == 0)
{
lean_dec_ref(x_693);
x_685 = lean_box(0);
goto block_692;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec_ref(x_684);
lean_dec(x_3);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 x_695 = x_693;
} else {
 lean_dec_ref(x_693);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
block_709:
{
uint8_t x_700; 
x_700 = lean_nat_dec_lt(x_606, x_698);
if (x_700 == 0)
{
lean_dec_ref(x_683);
lean_dec(x_6);
x_685 = lean_box(0);
goto block_692;
}
else
{
lean_object* x_701; uint8_t x_702; 
x_701 = lean_box(0);
x_702 = lean_nat_dec_le(x_698, x_698);
if (x_702 == 0)
{
if (x_700 == 0)
{
lean_dec_ref(x_683);
lean_dec(x_6);
x_685 = lean_box(0);
goto block_692;
}
else
{
size_t x_703; size_t x_704; lean_object* x_705; 
x_703 = 0;
x_704 = lean_usize_of_nat(x_698);
x_705 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_683, x_703, x_704, x_701, x_6);
lean_dec(x_6);
lean_dec_ref(x_683);
x_693 = x_705;
goto block_697;
}
}
else
{
size_t x_706; size_t x_707; lean_object* x_708; 
x_706 = 0;
x_707 = lean_usize_of_nat(x_698);
x_708 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_683, x_706, x_707, x_701, x_6);
lean_dec(x_6);
lean_dec_ref(x_683);
x_693 = x_708;
goto block_697;
}
}
}
block_712:
{
if (x_710 == 0)
{
lean_inc_ref(x_684);
lean_inc_ref(x_683);
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_699 = lean_box(0);
goto block_709;
}
else
{
if (x_122 == 0)
{
x_658 = x_3;
x_659 = x_5;
x_660 = x_6;
x_661 = x_7;
x_662 = x_8;
x_663 = lean_box(0);
goto block_679;
}
else
{
lean_inc_ref(x_684);
lean_inc_ref(x_683);
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_699 = lean_box(0);
goto block_709;
}
}
}
}
else
{
lean_object* x_722; lean_object* x_723; 
lean_inc_ref(x_682);
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_722 = lean_ctor_get(x_682, 0);
lean_inc_ref(x_722);
lean_dec_ref(x_682);
x_723 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_723, 0, x_722);
return x_723;
}
}
block_624:
{
lean_object* x_617; 
x_617 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_615);
lean_dec(x_615);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 x_618 = x_617;
} else {
 lean_dec_ref(x_617);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_619 = lean_alloc_ctor(6, 1, 0);
} else {
 x_619 = x_604;
 lean_ctor_set_tag(x_619, 6);
}
lean_ctor_set(x_619, 0, x_614);
if (lean_is_scalar(x_618)) {
 x_620 = lean_alloc_ctor(0, 1, 0);
} else {
 x_620 = x_618;
}
lean_ctor_set(x_620, 0, x_619);
return x_620;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec_ref(x_614);
lean_dec(x_604);
x_621 = lean_ctor_get(x_617, 0);
lean_inc(x_621);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 x_622 = x_617;
} else {
 lean_dec_ref(x_617);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 1, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_621);
return x_623;
}
}
block_630:
{
if (lean_obj_tag(x_626) == 0)
{
lean_dec_ref(x_626);
x_615 = x_625;
x_616 = lean_box(0);
goto block_624;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_625);
lean_dec_ref(x_614);
lean_dec(x_604);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 x_628 = x_626;
} else {
 lean_dec_ref(x_626);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 1, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_627);
return x_629;
}
}
block_647:
{
uint8_t x_638; 
x_638 = lean_nat_dec_lt(x_606, x_634);
if (x_638 == 0)
{
lean_dec(x_636);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec_ref(x_632);
lean_dec(x_631);
lean_dec(x_611);
x_615 = x_635;
x_616 = lean_box(0);
goto block_624;
}
else
{
lean_object* x_639; uint8_t x_640; 
x_639 = lean_box(0);
x_640 = lean_nat_dec_le(x_634, x_634);
if (x_640 == 0)
{
if (x_638 == 0)
{
lean_dec(x_636);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec_ref(x_632);
lean_dec(x_631);
lean_dec(x_611);
x_615 = x_635;
x_616 = lean_box(0);
goto block_624;
}
else
{
size_t x_641; size_t x_642; lean_object* x_643; 
x_641 = 0;
x_642 = lean_usize_of_nat(x_634);
lean_dec(x_634);
x_643 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_611, x_641, x_642, x_639, x_633, x_636, x_632, x_631);
lean_dec(x_631);
lean_dec_ref(x_632);
lean_dec(x_636);
lean_dec_ref(x_633);
lean_dec(x_611);
x_625 = x_635;
x_626 = x_643;
goto block_630;
}
}
else
{
size_t x_644; size_t x_645; lean_object* x_646; 
x_644 = 0;
x_645 = lean_usize_of_nat(x_634);
lean_dec(x_634);
x_646 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_611, x_644, x_645, x_639, x_633, x_636, x_632, x_631);
lean_dec(x_631);
lean_dec_ref(x_632);
lean_dec(x_636);
lean_dec_ref(x_633);
lean_dec(x_611);
x_625 = x_635;
x_626 = x_646;
goto block_630;
}
}
}
block_652:
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
if (lean_is_scalar(x_598)) {
 x_649 = lean_alloc_ctor(0, 4, 0);
} else {
 x_649 = x_598;
}
lean_ctor_set(x_649, 0, x_594);
lean_ctor_set(x_649, 1, x_614);
lean_ctor_set(x_649, 2, x_603);
lean_ctor_set(x_649, 3, x_611);
x_650 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_650, 0, x_649);
if (lean_is_scalar(x_612)) {
 x_651 = lean_alloc_ctor(0, 1, 0);
} else {
 x_651 = x_612;
}
lean_ctor_set(x_651, 0, x_650);
return x_651;
}
block_657:
{
if (x_654 == 0)
{
lean_dec(x_609);
lean_dec(x_596);
lean_dec_ref(x_1);
x_648 = lean_box(0);
goto block_652;
}
else
{
uint8_t x_655; 
x_655 = l_Lean_instBEqFVarId_beq(x_596, x_603);
lean_dec(x_596);
if (x_655 == 0)
{
lean_dec(x_609);
lean_dec_ref(x_1);
x_648 = lean_box(0);
goto block_652;
}
else
{
lean_object* x_656; 
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_603);
lean_dec(x_598);
lean_dec(x_594);
if (lean_is_scalar(x_609)) {
 x_656 = lean_alloc_ctor(0, 1, 0);
} else {
 x_656 = x_609;
}
lean_ctor_set(x_656, 0, x_1);
return x_656;
}
}
}
block_679:
{
lean_object* x_664; uint8_t x_665; 
x_664 = lean_array_get_size(x_611);
x_665 = lean_nat_dec_lt(x_606, x_664);
if (x_665 == 0)
{
lean_dec(x_612);
lean_dec(x_609);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_631 = x_662;
x_632 = x_661;
x_633 = x_659;
x_634 = x_664;
x_635 = x_658;
x_636 = x_660;
x_637 = lean_box(0);
goto block_647;
}
else
{
if (x_665 == 0)
{
lean_dec(x_612);
lean_dec(x_609);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_631 = x_662;
x_632 = x_661;
x_633 = x_659;
x_634 = x_664;
x_635 = x_658;
x_636 = x_660;
x_637 = lean_box(0);
goto block_647;
}
else
{
size_t x_666; size_t x_667; uint8_t x_668; 
x_666 = 0;
x_667 = lean_usize_of_nat(x_664);
x_668 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_109, x_110, x_611, x_666, x_667);
lean_dec(x_110);
lean_dec(x_109);
if (x_668 == 0)
{
lean_dec(x_612);
lean_dec(x_609);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_1);
x_631 = x_662;
x_632 = x_661;
x_633 = x_659;
x_634 = x_664;
x_635 = x_658;
x_636 = x_660;
x_637 = lean_box(0);
goto block_647;
}
else
{
if (x_122 == 0)
{
lean_object* x_669; 
lean_dec(x_662);
lean_dec_ref(x_661);
lean_dec(x_660);
lean_dec_ref(x_659);
lean_dec(x_604);
lean_inc(x_603);
x_669 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_603, x_658);
lean_dec(x_658);
if (lean_obj_tag(x_669) == 0)
{
size_t x_670; size_t x_671; uint8_t x_672; 
lean_dec_ref(x_669);
x_670 = lean_ptr_addr(x_597);
lean_dec_ref(x_597);
x_671 = lean_ptr_addr(x_611);
x_672 = lean_usize_dec_eq(x_670, x_671);
if (x_672 == 0)
{
lean_dec_ref(x_595);
x_653 = lean_box(0);
x_654 = x_672;
goto block_657;
}
else
{
size_t x_673; size_t x_674; uint8_t x_675; 
x_673 = lean_ptr_addr(x_595);
lean_dec_ref(x_595);
x_674 = lean_ptr_addr(x_614);
x_675 = lean_usize_dec_eq(x_673, x_674);
x_653 = lean_box(0);
x_654 = x_675;
goto block_657;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec_ref(x_614);
lean_dec(x_612);
lean_dec(x_611);
lean_dec(x_609);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_1);
x_676 = lean_ctor_get(x_669, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 x_677 = x_669;
} else {
 lean_dec_ref(x_669);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 1, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_676);
return x_678;
}
}
else
{
lean_dec(x_612);
lean_dec(x_609);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_1);
x_631 = x_662;
x_632 = x_661;
x_633 = x_659;
x_634 = x_664;
x_635 = x_658;
x_636 = x_660;
x_637 = lean_box(0);
goto block_647;
}
}
}
}
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_609);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_724 = lean_ctor_get(x_610, 0);
lean_inc(x_724);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_725 = x_610;
} else {
 lean_dec_ref(x_610);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 1, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_724);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_727 = lean_ctor_get(x_607, 0);
lean_inc(x_727);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_728 = x_607;
} else {
 lean_dec_ref(x_607);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 1, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_727);
return x_729;
}
}
else
{
lean_object* x_730; 
lean_dec(x_598);
lean_dec_ref(x_597);
lean_dec(x_596);
lean_dec_ref(x_595);
lean_dec(x_594);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_730 = l_Lean_Compiler_LCNF_mkReturnErased(x_601, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_730;
}
}
}
}
else
{
uint8_t x_731; 
lean_dec_ref(x_447);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_731 = !lean_is_exclusive(x_448);
if (x_731 == 0)
{
return x_448;
}
else
{
lean_object* x_732; lean_object* x_733; 
x_732 = lean_ctor_get(x_448, 0);
lean_inc(x_732);
lean_dec(x_448);
x_733 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_733, 0, x_732);
return x_733;
}
}
}
case 5:
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_free_object(x_138);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_734 = lean_ctor_get(x_1, 0);
x_735 = lean_st_ref_get(x_3);
x_736 = lean_ctor_get(x_735, 0);
lean_inc_ref(x_736);
lean_dec(x_735);
lean_inc(x_734);
x_737 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_736, x_734, x_122);
lean_dec_ref(x_736);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
lean_dec_ref(x_737);
lean_inc(x_738);
x_739 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_738, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_739) == 0)
{
uint8_t x_740; 
x_740 = !lean_is_exclusive(x_739);
if (x_740 == 0)
{
lean_object* x_741; uint8_t x_742; 
x_741 = lean_ctor_get(x_739, 0);
lean_dec(x_741);
x_742 = l_Lean_instBEqFVarId_beq(x_734, x_738);
if (x_742 == 0)
{
uint8_t x_743; 
x_743 = !lean_is_exclusive(x_1);
if (x_743 == 0)
{
lean_object* x_744; 
x_744 = lean_ctor_get(x_1, 0);
lean_dec(x_744);
lean_ctor_set(x_1, 0, x_738);
lean_ctor_set(x_739, 0, x_1);
return x_739;
}
else
{
lean_object* x_745; 
lean_dec(x_1);
x_745 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_745, 0, x_738);
lean_ctor_set(x_739, 0, x_745);
return x_739;
}
}
else
{
lean_dec(x_738);
lean_ctor_set(x_739, 0, x_1);
return x_739;
}
}
else
{
uint8_t x_746; 
lean_dec(x_739);
x_746 = l_Lean_instBEqFVarId_beq(x_734, x_738);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_747 = x_1;
} else {
 lean_dec_ref(x_1);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(5, 1, 0);
} else {
 x_748 = x_747;
}
lean_ctor_set(x_748, 0, x_738);
x_749 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_749, 0, x_748);
return x_749;
}
else
{
lean_object* x_750; 
lean_dec(x_738);
x_750 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_750, 0, x_1);
return x_750;
}
}
}
else
{
uint8_t x_751; 
lean_dec(x_738);
lean_dec_ref(x_1);
x_751 = !lean_is_exclusive(x_739);
if (x_751 == 0)
{
return x_739;
}
else
{
lean_object* x_752; lean_object* x_753; 
x_752 = lean_ctor_get(x_739, 0);
lean_inc(x_752);
lean_dec(x_739);
x_753 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_753, 0, x_752);
return x_753;
}
}
}
else
{
uint8_t x_754; lean_object* x_755; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_754 = 0;
x_755 = l_Lean_Compiler_LCNF_mkReturnErased(x_754, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_755;
}
}
case 6:
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; lean_object* x_760; size_t x_761; size_t x_762; uint8_t x_763; 
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_756 = lean_ctor_get(x_1, 0);
x_757 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_758 = lean_ctor_get(x_757, 0);
lean_inc_ref(x_758);
lean_dec(x_757);
x_759 = 0;
lean_inc_ref(x_756);
x_760 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_759, x_758, x_122, x_756);
lean_dec_ref(x_758);
x_761 = lean_ptr_addr(x_756);
x_762 = lean_ptr_addr(x_760);
x_763 = lean_usize_dec_eq(x_761, x_762);
if (x_763 == 0)
{
uint8_t x_764; 
x_764 = !lean_is_exclusive(x_1);
if (x_764 == 0)
{
lean_object* x_765; 
x_765 = lean_ctor_get(x_1, 0);
lean_dec(x_765);
lean_ctor_set(x_1, 0, x_760);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
else
{
lean_object* x_766; 
lean_dec(x_1);
x_766 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_766, 0, x_760);
lean_ctor_set(x_138, 0, x_766);
return x_138;
}
}
else
{
lean_dec_ref(x_760);
lean_ctor_set(x_138, 0, x_1);
return x_138;
}
}
default: 
{
lean_object* x_767; lean_object* x_768; 
lean_free_object(x_138);
lean_dec(x_110);
lean_dec(x_109);
x_767 = lean_ctor_get(x_1, 0);
x_768 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_768);
lean_inc_ref(x_767);
x_141 = x_767;
x_142 = x_768;
x_143 = x_2;
x_144 = x_3;
x_145 = x_4;
x_146 = x_5;
x_147 = x_6;
x_148 = x_7;
x_149 = x_8;
goto block_189;
}
}
block_189:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_141, 0);
x_151 = lean_ctor_get(x_141, 2);
x_152 = lean_ctor_get(x_141, 3);
x_153 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_150, x_144);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = 0;
x_156 = lean_unbox(x_154);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = lean_unbox(x_154);
lean_dec(x_154);
x_81 = x_142;
x_82 = x_158;
x_83 = x_141;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_159; 
lean_inc_ref(x_152);
x_159 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_152, x_151);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_unbox(x_154);
lean_dec(x_154);
x_81 = x_142;
x_82 = x_160;
x_83 = x_141;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_st_ref_get(x_144);
x_162 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_162);
lean_dec(x_161);
x_163 = l_Lean_Compiler_LCNF_normFunDeclImp(x_155, x_122, x_141, x_162, x_146, x_147, x_148, x_149);
lean_dec_ref(x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc_ref(x_146);
x_165 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_164, x_146, x_147, x_148, x_149);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_144);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
lean_dec_ref(x_167);
x_168 = lean_unbox(x_154);
lean_dec(x_154);
x_81 = x_142;
x_82 = x_168;
x_83 = x_166;
x_84 = x_143;
x_85 = x_144;
x_86 = x_145;
x_87 = x_146;
x_88 = x_147;
x_89 = x_148;
x_90 = x_149;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_169; 
lean_dec(x_166);
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
return x_167;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_172 = !lean_is_exclusive(x_165);
if (x_172 == 0)
{
return x_165;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_165, 0);
lean_inc(x_173);
lean_dec(x_165);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_175 = !lean_is_exclusive(x_163);
if (x_175 == 0)
{
return x_163;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_163, 0);
lean_inc(x_176);
lean_dec(x_163);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_st_ref_get(x_144);
x_179 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_179);
lean_dec(x_178);
x_180 = l_Lean_Compiler_LCNF_normFunDeclImp(x_155, x_122, x_141, x_179, x_146, x_147, x_148, x_149);
lean_dec_ref(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_unbox(x_154);
lean_dec(x_154);
x_49 = x_142;
x_50 = x_182;
x_51 = x_181;
x_52 = x_143;
x_53 = x_144;
x_54 = x_145;
x_55 = x_146;
x_56 = x_147;
x_57 = x_148;
x_58 = x_149;
x_59 = lean_box(0);
goto block_80;
}
else
{
uint8_t x_183; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_180);
if (x_183 == 0)
{
return x_180;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_1);
x_186 = !lean_is_exclusive(x_153);
if (x_186 == 0)
{
return x_153;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_153, 0);
lean_inc(x_187);
lean_dec(x_153);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_818; lean_object* x_819; 
lean_dec(x_138);
x_818 = lean_unsigned_to_nat(1u);
x_819 = lean_nat_add(x_109, x_818);
lean_inc(x_110);
lean_ctor_set(x_7, 3, x_819);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; uint8_t x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_963; 
lean_dec(x_110);
lean_dec(x_109);
x_820 = lean_ctor_get(x_1, 0);
x_821 = lean_ctor_get(x_1, 1);
x_947 = 0;
lean_inc_ref(x_820);
x_963 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_947, x_122, x_820, x_3, x_6);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_998; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
lean_dec_ref(x_963);
lean_inc(x_964);
lean_inc_ref(x_820);
x_998 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_947, x_820, x_964);
if (x_998 == 0)
{
goto block_997;
}
else
{
if (x_122 == 0)
{
x_965 = x_2;
x_966 = x_3;
x_967 = x_4;
x_968 = x_5;
x_969 = x_6;
x_970 = x_7;
x_971 = x_8;
x_972 = lean_box(0);
goto block_992;
}
else
{
goto block_997;
}
}
block_992:
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_973 = lean_ctor_get(x_964, 2);
x_974 = lean_ctor_get(x_964, 3);
lean_inc(x_971);
lean_inc_ref(x_970);
lean_inc(x_969);
lean_inc_ref(x_968);
lean_inc_ref(x_967);
lean_inc(x_974);
x_975 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_974, x_965, x_967, x_968, x_969, x_970, x_971);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
lean_dec_ref(x_975);
if (lean_obj_tag(x_976) == 1)
{
lean_object* x_977; lean_object* x_978; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
lean_dec_ref(x_976);
x_978 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_966);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; 
lean_dec_ref(x_978);
x_979 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_947, x_964, x_977, x_969);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
lean_dec_ref(x_979);
x_981 = lean_ctor_get(x_980, 2);
lean_inc_ref(x_981);
x_982 = lean_ctor_get(x_980, 3);
lean_inc(x_982);
x_948 = x_980;
x_949 = x_981;
x_950 = x_982;
x_951 = x_965;
x_952 = x_966;
x_953 = x_967;
x_954 = x_968;
x_955 = x_969;
x_956 = x_970;
x_957 = x_971;
x_958 = lean_box(0);
goto block_962;
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_971);
lean_dec_ref(x_970);
lean_dec(x_969);
lean_dec_ref(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec_ref(x_1);
x_983 = lean_ctor_get(x_979, 0);
lean_inc(x_983);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 x_984 = x_979;
} else {
 lean_dec_ref(x_979);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 1, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_983);
return x_985;
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_977);
lean_dec(x_971);
lean_dec_ref(x_970);
lean_dec(x_969);
lean_dec_ref(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_1);
x_986 = lean_ctor_get(x_978, 0);
lean_inc(x_986);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 x_987 = x_978;
} else {
 lean_dec_ref(x_978);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 1, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_986);
return x_988;
}
}
else
{
lean_dec(x_976);
lean_inc(x_974);
lean_inc_ref(x_973);
x_948 = x_964;
x_949 = x_973;
x_950 = x_974;
x_951 = x_965;
x_952 = x_966;
x_953 = x_967;
x_954 = x_968;
x_955 = x_969;
x_956 = x_970;
x_957 = x_971;
x_958 = lean_box(0);
goto block_962;
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_971);
lean_dec_ref(x_970);
lean_dec(x_969);
lean_dec_ref(x_968);
lean_dec_ref(x_967);
lean_dec(x_966);
lean_dec_ref(x_965);
lean_dec(x_964);
lean_dec_ref(x_1);
x_989 = lean_ctor_get(x_975, 0);
lean_inc(x_989);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 x_990 = x_975;
} else {
 lean_dec_ref(x_975);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 1, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_989);
return x_991;
}
}
block_997:
{
lean_object* x_993; 
x_993 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_993) == 0)
{
lean_dec_ref(x_993);
x_965 = x_2;
x_966 = x_3;
x_967 = x_4;
x_968 = x_5;
x_969 = x_6;
x_970 = x_7;
x_971 = x_8;
x_972 = lean_box(0);
goto block_992;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_964);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
if (lean_is_exclusive(x_993)) {
 lean_ctor_release(x_993, 0);
 x_995 = x_993;
} else {
 lean_dec_ref(x_993);
 x_995 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_996 = lean_alloc_ctor(1, 1, 0);
} else {
 x_996 = x_995;
}
lean_ctor_set(x_996, 0, x_994);
return x_996;
}
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_999 = lean_ctor_get(x_963, 0);
lean_inc(x_999);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 x_1000 = x_963;
} else {
 lean_dec_ref(x_963);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_999);
return x_1001;
}
block_946:
{
if (x_831 == 0)
{
lean_object* x_832; 
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_824);
x_832 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_824, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
lean_dec_ref(x_832);
if (lean_obj_tag(x_833) == 1)
{
lean_object* x_834; lean_object* x_835; 
lean_dec_ref(x_824);
lean_inc_ref(x_821);
lean_dec_ref(x_1);
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
lean_dec_ref(x_833);
x_835 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_827);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; 
lean_dec_ref(x_835);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_830);
lean_inc(x_827);
lean_inc_ref(x_826);
x_836 = l_Lean_Compiler_LCNF_Simp_simp(x_821, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; lean_object* x_838; 
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
lean_dec_ref(x_836);
x_838 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_834, x_837, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
lean_dec(x_829);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_825);
lean_dec_ref(x_830);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec(x_834);
return x_838;
}
else
{
lean_dec(x_834);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
return x_836;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_834);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_839 = lean_ctor_get(x_835, 0);
lean_inc(x_839);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 x_840 = x_835;
} else {
 lean_dec_ref(x_835);
 x_840 = lean_box(0);
}
if (lean_is_scalar(x_840)) {
 x_841 = lean_alloc_ctor(1, 1, 0);
} else {
 x_841 = x_840;
}
lean_ctor_set(x_841, 0, x_839);
return x_841;
}
}
else
{
lean_object* x_842; 
lean_dec(x_833);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_824);
x_842 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_824, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
lean_dec_ref(x_842);
if (lean_obj_tag(x_843) == 1)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec_ref(x_824);
lean_inc_ref(x_821);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_844 = x_1;
} else {
 lean_dec_ref(x_1);
 x_844 = lean_box(0);
}
x_845 = lean_ctor_get(x_843, 0);
lean_inc(x_845);
lean_dec_ref(x_843);
if (lean_is_scalar(x_844)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_844;
 lean_ctor_set_tag(x_846, 1);
}
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_821);
x_1 = x_846;
x_2 = x_826;
x_3 = x_827;
x_4 = x_830;
x_5 = x_825;
x_6 = x_822;
x_7 = x_823;
x_8 = x_829;
goto _start;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_843);
x_848 = lean_ctor_get(x_824, 0);
x_849 = lean_ctor_get(x_824, 3);
x_850 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_849);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
lean_dec_ref(x_850);
if (lean_obj_tag(x_851) == 1)
{
lean_object* x_852; lean_object* x_853; 
lean_inc_ref(x_821);
lean_dec_ref(x_1);
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
lean_dec_ref(x_851);
lean_inc(x_848);
x_853 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_848, x_852, x_827, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; 
lean_dec_ref(x_853);
x_854 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_824, x_827, x_822);
lean_dec_ref(x_824);
if (lean_obj_tag(x_854) == 0)
{
lean_dec_ref(x_854);
x_1 = x_821;
x_2 = x_826;
x_3 = x_827;
x_4 = x_830;
x_5 = x_825;
x_6 = x_822;
x_7 = x_823;
x_8 = x_829;
goto _start;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_856 = lean_ctor_get(x_854, 0);
lean_inc(x_856);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 x_857 = x_854;
} else {
 lean_dec_ref(x_854);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 1, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_856);
return x_858;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_859 = lean_ctor_get(x_853, 0);
lean_inc(x_859);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 x_860 = x_853;
} else {
 lean_dec_ref(x_853);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 1, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_859);
return x_861;
}
}
else
{
lean_object* x_862; 
lean_dec(x_851);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_830);
lean_inc(x_827);
lean_inc_ref(x_826);
lean_inc_ref(x_821);
lean_inc_ref(x_824);
x_862 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_824, x_821, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
lean_dec_ref(x_862);
if (lean_obj_tag(x_863) == 1)
{
lean_object* x_864; lean_object* x_865; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec_ref(x_1);
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
lean_dec_ref(x_863);
x_865 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_824, x_827, x_822);
lean_dec(x_822);
lean_dec(x_827);
lean_dec_ref(x_824);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; 
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 x_866 = x_865;
} else {
 lean_dec_ref(x_865);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(0, 1, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
return x_867;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_864);
x_868 = lean_ctor_get(x_865, 0);
lean_inc(x_868);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 x_869 = x_865;
} else {
 lean_dec_ref(x_865);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(1, 1, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_868);
return x_870;
}
}
else
{
lean_object* x_871; 
lean_dec(x_863);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_830);
lean_inc(x_827);
lean_inc_ref(x_826);
lean_inc(x_849);
x_871 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_849, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
lean_dec_ref(x_871);
if (lean_obj_tag(x_872) == 1)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_inc_ref(x_821);
lean_dec_ref(x_1);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
lean_dec_ref(x_872);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
lean_inc(x_848);
x_876 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_848, x_875, x_827, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
lean_dec_ref(x_876);
x_877 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_824, x_827, x_822);
lean_dec_ref(x_824);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; 
lean_dec_ref(x_877);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_830);
lean_inc(x_827);
lean_inc_ref(x_826);
x_878 = l_Lean_Compiler_LCNF_Simp_simp(x_821, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
lean_dec_ref(x_878);
x_880 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_874, x_879, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
lean_dec(x_829);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_825);
lean_dec_ref(x_830);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec(x_874);
return x_880;
}
else
{
lean_dec(x_874);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
return x_878;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_874);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_881 = lean_ctor_get(x_877, 0);
lean_inc(x_881);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 x_882 = x_877;
} else {
 lean_dec_ref(x_877);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 1, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_874);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_884 = lean_ctor_get(x_876, 0);
lean_inc(x_884);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 x_885 = x_876;
} else {
 lean_dec_ref(x_876);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 1, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_884);
return x_886;
}
}
else
{
lean_object* x_887; 
lean_dec(x_872);
lean_inc(x_829);
lean_inc_ref(x_823);
lean_inc(x_822);
lean_inc_ref(x_825);
lean_inc_ref(x_830);
lean_inc(x_827);
lean_inc_ref(x_826);
lean_inc_ref(x_821);
x_887 = l_Lean_Compiler_LCNF_Simp_simp(x_821, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
lean_dec_ref(x_887);
x_889 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_848, x_827);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; uint8_t x_891; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
lean_dec_ref(x_889);
x_891 = lean_unbox(x_890);
lean_dec(x_890);
if (x_891 == 0)
{
lean_object* x_892; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec_ref(x_1);
x_892 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_824, x_827, x_822);
lean_dec(x_822);
lean_dec(x_827);
lean_dec_ref(x_824);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; 
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 x_893 = x_892;
} else {
 lean_dec_ref(x_892);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(0, 1, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_888);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_888);
x_895 = lean_ctor_get(x_892, 0);
lean_inc(x_895);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 x_896 = x_892;
} else {
 lean_dec_ref(x_892);
 x_896 = lean_box(0);
}
if (lean_is_scalar(x_896)) {
 x_897 = lean_alloc_ctor(1, 1, 0);
} else {
 x_897 = x_896;
}
lean_ctor_set(x_897, 0, x_895);
return x_897;
}
}
else
{
lean_object* x_898; 
lean_inc_ref(x_824);
x_898 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_824, x_826, x_827, x_830, x_825, x_822, x_823, x_829);
lean_dec(x_829);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_825);
lean_dec_ref(x_830);
lean_dec(x_827);
lean_dec_ref(x_826);
if (lean_obj_tag(x_898) == 0)
{
size_t x_899; size_t x_900; uint8_t x_901; 
lean_dec_ref(x_898);
x_899 = lean_ptr_addr(x_821);
x_900 = lean_ptr_addr(x_888);
x_901 = lean_usize_dec_eq(x_899, x_900);
if (x_901 == 0)
{
x_98 = x_888;
x_99 = x_824;
x_100 = lean_box(0);
x_101 = x_901;
goto block_105;
}
else
{
size_t x_902; size_t x_903; uint8_t x_904; 
x_902 = lean_ptr_addr(x_820);
x_903 = lean_ptr_addr(x_824);
x_904 = lean_usize_dec_eq(x_902, x_903);
x_98 = x_888;
x_99 = x_824;
x_100 = lean_box(0);
x_101 = x_904;
goto block_105;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_888);
lean_dec_ref(x_824);
lean_dec_ref(x_1);
x_905 = lean_ctor_get(x_898, 0);
lean_inc(x_905);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 x_906 = x_898;
} else {
 lean_dec_ref(x_898);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(1, 1, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_905);
return x_907;
}
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_888);
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_908 = lean_ctor_get(x_889, 0);
lean_inc(x_908);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 x_909 = x_889;
} else {
 lean_dec_ref(x_889);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 1, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_908);
return x_910;
}
}
else
{
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
return x_887;
}
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_911 = lean_ctor_get(x_871, 0);
lean_inc(x_911);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 x_912 = x_871;
} else {
 lean_dec_ref(x_871);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 1, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_911);
return x_913;
}
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_914 = lean_ctor_get(x_862, 0);
lean_inc(x_914);
if (lean_is_exclusive(x_862)) {
 lean_ctor_release(x_862, 0);
 x_915 = x_862;
} else {
 lean_dec_ref(x_862);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 1, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_914);
return x_916;
}
}
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_917 = lean_ctor_get(x_850, 0);
lean_inc(x_917);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 x_918 = x_850;
} else {
 lean_dec_ref(x_850);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(1, 1, 0);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_917);
return x_919;
}
}
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_920 = lean_ctor_get(x_842, 0);
lean_inc(x_920);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 x_921 = x_842;
} else {
 lean_dec_ref(x_842);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(1, 1, 0);
} else {
 x_922 = x_921;
}
lean_ctor_set(x_922, 0, x_920);
return x_922;
}
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_824);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_1);
x_923 = lean_ctor_get(x_832, 0);
lean_inc(x_923);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 x_924 = x_832;
} else {
 lean_dec_ref(x_832);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 1, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_inc_ref(x_821);
lean_dec_ref(x_1);
x_926 = lean_st_ref_take(x_827);
x_927 = lean_ctor_get(x_824, 0);
x_928 = lean_ctor_get(x_926, 0);
lean_inc_ref(x_928);
x_929 = lean_ctor_get(x_926, 1);
lean_inc_ref(x_929);
x_930 = lean_ctor_get(x_926, 2);
lean_inc(x_930);
x_931 = lean_ctor_get(x_926, 3);
lean_inc_ref(x_931);
x_932 = lean_ctor_get_uint8(x_926, sizeof(void*)*7);
x_933 = lean_ctor_get(x_926, 4);
lean_inc(x_933);
x_934 = lean_ctor_get(x_926, 5);
lean_inc(x_934);
x_935 = lean_ctor_get(x_926, 6);
lean_inc(x_935);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 lean_ctor_release(x_926, 2);
 lean_ctor_release(x_926, 3);
 lean_ctor_release(x_926, 4);
 lean_ctor_release(x_926, 5);
 lean_ctor_release(x_926, 6);
 x_936 = x_926;
} else {
 lean_dec_ref(x_926);
 x_936 = lean_box(0);
}
x_937 = lean_box(0);
lean_inc(x_927);
x_938 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_928, x_927, x_937);
if (lean_is_scalar(x_936)) {
 x_939 = lean_alloc_ctor(0, 7, 1);
} else {
 x_939 = x_936;
}
lean_ctor_set(x_939, 0, x_938);
lean_ctor_set(x_939, 1, x_929);
lean_ctor_set(x_939, 2, x_930);
lean_ctor_set(x_939, 3, x_931);
lean_ctor_set(x_939, 4, x_933);
lean_ctor_set(x_939, 5, x_934);
lean_ctor_set(x_939, 6, x_935);
lean_ctor_set_uint8(x_939, sizeof(void*)*7, x_932);
x_940 = lean_st_ref_set(x_827, x_939);
x_941 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_824, x_827, x_822);
lean_dec_ref(x_824);
if (lean_obj_tag(x_941) == 0)
{
lean_dec_ref(x_941);
x_1 = x_821;
x_2 = x_826;
x_3 = x_827;
x_4 = x_830;
x_5 = x_825;
x_6 = x_822;
x_7 = x_823;
x_8 = x_829;
goto _start;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec_ref(x_830);
lean_dec(x_829);
lean_dec(x_827);
lean_dec_ref(x_826);
lean_dec_ref(x_825);
lean_dec_ref(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 x_944 = x_941;
} else {
 lean_dec_ref(x_941);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(1, 1, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_943);
return x_945;
}
}
}
block_962:
{
uint8_t x_959; 
x_959 = l_Lean_Expr_isErased(x_949);
lean_dec_ref(x_949);
if (x_959 == 0)
{
lean_dec(x_950);
x_822 = x_955;
x_823 = x_956;
x_824 = x_948;
x_825 = x_954;
x_826 = x_951;
x_827 = x_952;
x_828 = lean_box(0);
x_829 = x_957;
x_830 = x_953;
x_831 = x_122;
goto block_946;
}
else
{
lean_object* x_960; uint8_t x_961; 
x_960 = lean_box(1);
x_961 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_947, x_950, x_960);
if (x_961 == 0)
{
x_822 = x_955;
x_823 = x_956;
x_824 = x_948;
x_825 = x_954;
x_826 = x_951;
x_827 = x_952;
x_828 = lean_box(0);
x_829 = x_957;
x_830 = x_953;
x_831 = x_959;
goto block_946;
}
else
{
x_822 = x_955;
x_823 = x_956;
x_824 = x_948;
x_825 = x_954;
x_826 = x_951;
x_827 = x_952;
x_828 = lean_box(0);
x_829 = x_957;
x_830 = x_953;
x_831 = x_122;
goto block_946;
}
}
}
}
case 3:
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; uint8_t x_1006; lean_object* x_1007; 
lean_dec(x_110);
lean_dec(x_109);
x_1002 = lean_ctor_get(x_1, 0);
x_1003 = lean_ctor_get(x_1, 1);
x_1004 = lean_st_ref_get(x_3);
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc_ref(x_1005);
lean_dec(x_1004);
x_1006 = 0;
lean_inc(x_1002);
x_1007 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1005, x_1002, x_122);
lean_dec_ref(x_1005);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
lean_dec_ref(x_1007);
lean_inc_ref(x_1003);
x_1009 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1006, x_122, x_1003, x_3);
if (lean_obj_tag(x_1009) == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; lean_object* x_1019; lean_object* x_1025; lean_object* x_1030; 
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 x_1011 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1011 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1010);
x_1030 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1008, x_1010, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
lean_dec_ref(x_1030);
if (lean_obj_tag(x_1031) == 1)
{
lean_object* x_1032; 
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec_ref(x_1);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
lean_dec_ref(x_1031);
x_1 = x_1032;
goto _start;
}
else
{
lean_object* x_1034; 
lean_dec(x_1031);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1008);
x_1034 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1008, x_3);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; uint8_t x_1037; 
lean_dec_ref(x_1034);
x_1035 = lean_unsigned_to_nat(0u);
x_1036 = lean_array_get_size(x_1010);
x_1037 = lean_nat_dec_lt(x_1035, x_1036);
if (x_1037 == 0)
{
lean_dec(x_3);
x_1019 = lean_box(0);
goto block_1024;
}
else
{
lean_object* x_1038; uint8_t x_1039; 
x_1038 = lean_box(0);
x_1039 = lean_nat_dec_le(x_1036, x_1036);
if (x_1039 == 0)
{
if (x_1037 == 0)
{
lean_dec(x_3);
x_1019 = lean_box(0);
goto block_1024;
}
else
{
size_t x_1040; size_t x_1041; lean_object* x_1042; 
x_1040 = 0;
x_1041 = lean_usize_of_nat(x_1036);
x_1042 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1010, x_1040, x_1041, x_1038, x_3);
lean_dec(x_3);
x_1025 = x_1042;
goto block_1029;
}
}
else
{
size_t x_1043; size_t x_1044; lean_object* x_1045; 
x_1043 = 0;
x_1044 = lean_usize_of_nat(x_1036);
x_1045 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1010, x_1043, x_1044, x_1038, x_3);
lean_dec(x_3);
x_1025 = x_1045;
goto block_1029;
}
}
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1046 = lean_ctor_get(x_1034, 0);
lean_inc(x_1046);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 x_1047 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1046);
return x_1048;
}
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1049 = lean_ctor_get(x_1030, 0);
lean_inc(x_1049);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 x_1050 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1049);
return x_1051;
}
block_1018:
{
if (x_1013 == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1014 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1014 = lean_box(0);
}
if (lean_is_scalar(x_1014)) {
 x_1015 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1015 = x_1014;
}
lean_ctor_set(x_1015, 0, x_1008);
lean_ctor_set(x_1015, 1, x_1010);
if (lean_is_scalar(x_1011)) {
 x_1016 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1016 = x_1011;
}
lean_ctor_set(x_1016, 0, x_1015);
return x_1016;
}
else
{
lean_object* x_1017; 
lean_dec(x_1010);
lean_dec(x_1008);
if (lean_is_scalar(x_1011)) {
 x_1017 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1017 = x_1011;
}
lean_ctor_set(x_1017, 0, x_1);
return x_1017;
}
}
block_1024:
{
uint8_t x_1020; 
x_1020 = l_Lean_instBEqFVarId_beq(x_1002, x_1008);
if (x_1020 == 0)
{
x_1012 = lean_box(0);
x_1013 = x_1020;
goto block_1018;
}
else
{
size_t x_1021; size_t x_1022; uint8_t x_1023; 
x_1021 = lean_ptr_addr(x_1003);
x_1022 = lean_ptr_addr(x_1010);
x_1023 = lean_usize_dec_eq(x_1021, x_1022);
x_1012 = lean_box(0);
x_1013 = x_1023;
goto block_1018;
}
}
block_1029:
{
if (lean_obj_tag(x_1025) == 0)
{
lean_dec_ref(x_1025);
x_1019 = lean_box(0);
goto block_1024;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1008);
lean_dec_ref(x_1);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 x_1027 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1027 = lean_box(0);
}
if (lean_is_scalar(x_1027)) {
 x_1028 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1028 = x_1027;
}
lean_ctor_set(x_1028, 0, x_1026);
return x_1028;
}
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1008);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1052 = lean_ctor_get(x_1009, 0);
lean_inc(x_1052);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 x_1053 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1052);
return x_1054;
}
}
else
{
lean_object* x_1055; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1055 = l_Lean_Compiler_LCNF_mkReturnErased(x_1006, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1055;
}
}
case 4:
{
lean_object* x_1056; lean_object* x_1057; 
x_1056 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1056);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1056);
x_1057 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1056, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; 
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 x_1059 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1059 = lean_box(0);
}
if (lean_obj_tag(x_1058) == 1)
{
lean_object* x_1060; lean_object* x_1061; 
lean_dec_ref(x_1056);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1060 = lean_ctor_get(x_1058, 0);
lean_inc(x_1060);
lean_dec_ref(x_1058);
if (lean_is_scalar(x_1059)) {
 x_1061 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1061 = x_1059;
}
lean_ctor_set(x_1061, 0, x_1060);
return x_1061;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; 
lean_dec(x_1058);
x_1062 = lean_ctor_get(x_1056, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1056, 1);
lean_inc_ref(x_1063);
x_1064 = lean_ctor_get(x_1056, 2);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1056, 3);
lean_inc_ref(x_1065);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 lean_ctor_release(x_1056, 2);
 lean_ctor_release(x_1056, 3);
 x_1066 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1066 = lean_box(0);
}
x_1067 = lean_st_ref_get(x_3);
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc_ref(x_1068);
lean_dec(x_1067);
x_1069 = 0;
lean_inc(x_1064);
x_1070 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1068, x_1064, x_122);
lean_dec_ref(x_1068);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1072 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1072 = lean_box(0);
}
x_1073 = lean_st_ref_get(x_3);
x_1074 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1065);
lean_inc(x_1071);
x_1075 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1071, x_109, x_110, x_1074, x_1065, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 x_1077 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1077 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1078 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1076, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_1078) == 0)
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1093; lean_object* x_1094; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1116; lean_object* x_1121; uint8_t x_1122; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1148; uint8_t x_1149; 
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 x_1080 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1080 = lean_box(0);
}
x_1081 = lean_ctor_get(x_1073, 0);
lean_inc_ref(x_1081);
lean_dec(x_1073);
lean_inc_ref(x_1063);
x_1082 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1069, x_1081, x_122, x_1063);
lean_dec_ref(x_1081);
x_1148 = lean_array_get_size(x_1079);
x_1149 = lean_nat_dec_eq(x_1148, x_818);
if (x_1149 == 0)
{
lean_dec(x_1059);
x_1126 = x_3;
x_1127 = x_5;
x_1128 = x_6;
x_1129 = x_7;
x_1130 = x_8;
x_1131 = lean_box(0);
goto block_1147;
}
else
{
lean_object* x_1150; 
x_1150 = lean_array_fget_borrowed(x_1079, x_1074);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1161; lean_object* x_1166; lean_object* x_1167; uint8_t x_1178; lean_object* x_1179; uint8_t x_1181; 
lean_dec(x_1059);
x_1151 = lean_ctor_get(x_1150, 1);
x_1152 = lean_ctor_get(x_1150, 2);
x_1166 = lean_array_get_size(x_1151);
x_1181 = lean_nat_dec_lt(x_1074, x_1166);
if (x_1181 == 0)
{
x_1178 = x_122;
x_1179 = lean_box(0);
goto block_1180;
}
else
{
if (x_1181 == 0)
{
x_1178 = x_122;
x_1179 = lean_box(0);
goto block_1180;
}
else
{
size_t x_1182; size_t x_1183; lean_object* x_1184; 
x_1182 = 0;
x_1183 = lean_usize_of_nat(x_1166);
x_1184 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1151, x_1182, x_1183, x_3);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; uint8_t x_1186; 
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
lean_dec_ref(x_1184);
x_1186 = lean_unbox(x_1185);
lean_dec(x_1185);
x_1178 = x_1186;
x_1179 = lean_box(0);
goto block_1180;
}
else
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1077);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1187 = lean_ctor_get(x_1184, 0);
lean_inc(x_1187);
if (lean_is_exclusive(x_1184)) {
 lean_ctor_release(x_1184, 0);
 x_1188 = x_1184;
} else {
 lean_dec_ref(x_1184);
 x_1188 = lean_box(0);
}
if (lean_is_scalar(x_1188)) {
 x_1189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1189 = x_1188;
}
lean_ctor_set(x_1189, 0, x_1187);
return x_1189;
}
}
}
block_1160:
{
lean_object* x_1154; 
x_1154 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; 
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 x_1155 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1155 = lean_box(0);
}
if (lean_is_scalar(x_1155)) {
 x_1156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1156 = x_1155;
}
lean_ctor_set(x_1156, 0, x_1152);
return x_1156;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec_ref(x_1152);
x_1157 = lean_ctor_get(x_1154, 0);
lean_inc(x_1157);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 x_1158 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1157);
return x_1159;
}
}
block_1165:
{
if (lean_obj_tag(x_1161) == 0)
{
lean_dec_ref(x_1161);
x_1153 = lean_box(0);
goto block_1160;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec_ref(x_1152);
lean_dec(x_3);
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 x_1163 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1163 = lean_box(0);
}
if (lean_is_scalar(x_1163)) {
 x_1164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1164 = x_1163;
}
lean_ctor_set(x_1164, 0, x_1162);
return x_1164;
}
}
block_1177:
{
uint8_t x_1168; 
x_1168 = lean_nat_dec_lt(x_1074, x_1166);
if (x_1168 == 0)
{
lean_dec_ref(x_1151);
lean_dec(x_6);
x_1153 = lean_box(0);
goto block_1160;
}
else
{
lean_object* x_1169; uint8_t x_1170; 
x_1169 = lean_box(0);
x_1170 = lean_nat_dec_le(x_1166, x_1166);
if (x_1170 == 0)
{
if (x_1168 == 0)
{
lean_dec_ref(x_1151);
lean_dec(x_6);
x_1153 = lean_box(0);
goto block_1160;
}
else
{
size_t x_1171; size_t x_1172; lean_object* x_1173; 
x_1171 = 0;
x_1172 = lean_usize_of_nat(x_1166);
x_1173 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1151, x_1171, x_1172, x_1169, x_6);
lean_dec(x_6);
lean_dec_ref(x_1151);
x_1161 = x_1173;
goto block_1165;
}
}
else
{
size_t x_1174; size_t x_1175; lean_object* x_1176; 
x_1174 = 0;
x_1175 = lean_usize_of_nat(x_1166);
x_1176 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1151, x_1174, x_1175, x_1169, x_6);
lean_dec(x_6);
lean_dec_ref(x_1151);
x_1161 = x_1176;
goto block_1165;
}
}
}
block_1180:
{
if (x_1178 == 0)
{
lean_inc_ref(x_1152);
lean_inc_ref(x_1151);
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1077);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1167 = lean_box(0);
goto block_1177;
}
else
{
if (x_122 == 0)
{
x_1126 = x_3;
x_1127 = x_5;
x_1128 = x_6;
x_1129 = x_7;
x_1130 = x_8;
x_1131 = lean_box(0);
goto block_1147;
}
else
{
lean_inc_ref(x_1152);
lean_inc_ref(x_1151);
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1077);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1167 = lean_box(0);
goto block_1177;
}
}
}
}
else
{
lean_object* x_1190; lean_object* x_1191; 
lean_inc_ref(x_1150);
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1077);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1190 = lean_ctor_get(x_1150, 0);
lean_inc_ref(x_1190);
lean_dec_ref(x_1150);
if (lean_is_scalar(x_1059)) {
 x_1191 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1191 = x_1059;
}
lean_ctor_set(x_1191, 0, x_1190);
return x_1191;
}
}
block_1092:
{
lean_object* x_1085; 
x_1085 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1083);
lean_dec(x_1083);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 x_1086 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1087 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1087 = x_1072;
 lean_ctor_set_tag(x_1087, 6);
}
lean_ctor_set(x_1087, 0, x_1082);
if (lean_is_scalar(x_1086)) {
 x_1088 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1088 = x_1086;
}
lean_ctor_set(x_1088, 0, x_1087);
return x_1088;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
lean_dec_ref(x_1082);
lean_dec(x_1072);
x_1089 = lean_ctor_get(x_1085, 0);
lean_inc(x_1089);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 x_1090 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1091 = x_1090;
}
lean_ctor_set(x_1091, 0, x_1089);
return x_1091;
}
}
block_1098:
{
if (lean_obj_tag(x_1094) == 0)
{
lean_dec_ref(x_1094);
x_1083 = x_1093;
x_1084 = lean_box(0);
goto block_1092;
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1093);
lean_dec_ref(x_1082);
lean_dec(x_1072);
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
if (lean_is_exclusive(x_1094)) {
 lean_ctor_release(x_1094, 0);
 x_1096 = x_1094;
} else {
 lean_dec_ref(x_1094);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1096)) {
 x_1097 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1097 = x_1096;
}
lean_ctor_set(x_1097, 0, x_1095);
return x_1097;
}
}
block_1115:
{
uint8_t x_1106; 
x_1106 = lean_nat_dec_lt(x_1074, x_1102);
if (x_1106 == 0)
{
lean_dec(x_1104);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec_ref(x_1100);
lean_dec(x_1099);
lean_dec(x_1079);
x_1083 = x_1103;
x_1084 = lean_box(0);
goto block_1092;
}
else
{
lean_object* x_1107; uint8_t x_1108; 
x_1107 = lean_box(0);
x_1108 = lean_nat_dec_le(x_1102, x_1102);
if (x_1108 == 0)
{
if (x_1106 == 0)
{
lean_dec(x_1104);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec_ref(x_1100);
lean_dec(x_1099);
lean_dec(x_1079);
x_1083 = x_1103;
x_1084 = lean_box(0);
goto block_1092;
}
else
{
size_t x_1109; size_t x_1110; lean_object* x_1111; 
x_1109 = 0;
x_1110 = lean_usize_of_nat(x_1102);
lean_dec(x_1102);
x_1111 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1079, x_1109, x_1110, x_1107, x_1101, x_1104, x_1100, x_1099);
lean_dec(x_1099);
lean_dec_ref(x_1100);
lean_dec(x_1104);
lean_dec_ref(x_1101);
lean_dec(x_1079);
x_1093 = x_1103;
x_1094 = x_1111;
goto block_1098;
}
}
else
{
size_t x_1112; size_t x_1113; lean_object* x_1114; 
x_1112 = 0;
x_1113 = lean_usize_of_nat(x_1102);
lean_dec(x_1102);
x_1114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1079, x_1112, x_1113, x_1107, x_1101, x_1104, x_1100, x_1099);
lean_dec(x_1099);
lean_dec_ref(x_1100);
lean_dec(x_1104);
lean_dec_ref(x_1101);
lean_dec(x_1079);
x_1093 = x_1103;
x_1094 = x_1114;
goto block_1098;
}
}
}
block_1120:
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
if (lean_is_scalar(x_1066)) {
 x_1117 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1117 = x_1066;
}
lean_ctor_set(x_1117, 0, x_1062);
lean_ctor_set(x_1117, 1, x_1082);
lean_ctor_set(x_1117, 2, x_1071);
lean_ctor_set(x_1117, 3, x_1079);
x_1118 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1118, 0, x_1117);
if (lean_is_scalar(x_1080)) {
 x_1119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1119 = x_1080;
}
lean_ctor_set(x_1119, 0, x_1118);
return x_1119;
}
block_1125:
{
if (x_1122 == 0)
{
lean_dec(x_1077);
lean_dec(x_1064);
lean_dec_ref(x_1);
x_1116 = lean_box(0);
goto block_1120;
}
else
{
uint8_t x_1123; 
x_1123 = l_Lean_instBEqFVarId_beq(x_1064, x_1071);
lean_dec(x_1064);
if (x_1123 == 0)
{
lean_dec(x_1077);
lean_dec_ref(x_1);
x_1116 = lean_box(0);
goto block_1120;
}
else
{
lean_object* x_1124; 
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec(x_1062);
if (lean_is_scalar(x_1077)) {
 x_1124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1124 = x_1077;
}
lean_ctor_set(x_1124, 0, x_1);
return x_1124;
}
}
}
block_1147:
{
lean_object* x_1132; uint8_t x_1133; 
x_1132 = lean_array_get_size(x_1079);
x_1133 = lean_nat_dec_lt(x_1074, x_1132);
if (x_1133 == 0)
{
lean_dec(x_1080);
lean_dec(x_1077);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_1099 = x_1130;
x_1100 = x_1129;
x_1101 = x_1127;
x_1102 = x_1132;
x_1103 = x_1126;
x_1104 = x_1128;
x_1105 = lean_box(0);
goto block_1115;
}
else
{
if (x_1133 == 0)
{
lean_dec(x_1080);
lean_dec(x_1077);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_1099 = x_1130;
x_1100 = x_1129;
x_1101 = x_1127;
x_1102 = x_1132;
x_1103 = x_1126;
x_1104 = x_1128;
x_1105 = lean_box(0);
goto block_1115;
}
else
{
size_t x_1134; size_t x_1135; uint8_t x_1136; 
x_1134 = 0;
x_1135 = lean_usize_of_nat(x_1132);
x_1136 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_109, x_110, x_1079, x_1134, x_1135);
lean_dec(x_110);
lean_dec(x_109);
if (x_1136 == 0)
{
lean_dec(x_1080);
lean_dec(x_1077);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_1);
x_1099 = x_1130;
x_1100 = x_1129;
x_1101 = x_1127;
x_1102 = x_1132;
x_1103 = x_1126;
x_1104 = x_1128;
x_1105 = lean_box(0);
goto block_1115;
}
else
{
if (x_122 == 0)
{
lean_object* x_1137; 
lean_dec(x_1130);
lean_dec_ref(x_1129);
lean_dec(x_1128);
lean_dec_ref(x_1127);
lean_dec(x_1072);
lean_inc(x_1071);
x_1137 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1071, x_1126);
lean_dec(x_1126);
if (lean_obj_tag(x_1137) == 0)
{
size_t x_1138; size_t x_1139; uint8_t x_1140; 
lean_dec_ref(x_1137);
x_1138 = lean_ptr_addr(x_1065);
lean_dec_ref(x_1065);
x_1139 = lean_ptr_addr(x_1079);
x_1140 = lean_usize_dec_eq(x_1138, x_1139);
if (x_1140 == 0)
{
lean_dec_ref(x_1063);
x_1121 = lean_box(0);
x_1122 = x_1140;
goto block_1125;
}
else
{
size_t x_1141; size_t x_1142; uint8_t x_1143; 
x_1141 = lean_ptr_addr(x_1063);
lean_dec_ref(x_1063);
x_1142 = lean_ptr_addr(x_1082);
x_1143 = lean_usize_dec_eq(x_1141, x_1142);
x_1121 = lean_box(0);
x_1122 = x_1143;
goto block_1125;
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
lean_dec_ref(x_1082);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_1077);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_1);
x_1144 = lean_ctor_get(x_1137, 0);
lean_inc(x_1144);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 x_1145 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1145 = lean_box(0);
}
if (lean_is_scalar(x_1145)) {
 x_1146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1146 = x_1145;
}
lean_ctor_set(x_1146, 0, x_1144);
return x_1146;
}
}
else
{
lean_dec(x_1080);
lean_dec(x_1077);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec_ref(x_1);
x_1099 = x_1130;
x_1100 = x_1129;
x_1101 = x_1127;
x_1102 = x_1132;
x_1103 = x_1126;
x_1104 = x_1128;
x_1105 = lean_box(0);
goto block_1115;
}
}
}
}
}
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_1077);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec(x_1059);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1192 = lean_ctor_get(x_1078, 0);
lean_inc(x_1192);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 x_1193 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1193 = lean_box(0);
}
if (lean_is_scalar(x_1193)) {
 x_1194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1194 = x_1193;
}
lean_ctor_set(x_1194, 0, x_1192);
return x_1194;
}
}
else
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec(x_1059);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1195 = lean_ctor_get(x_1075, 0);
lean_inc(x_1195);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 x_1196 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1196 = lean_box(0);
}
if (lean_is_scalar(x_1196)) {
 x_1197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1197 = x_1196;
}
lean_ctor_set(x_1197, 0, x_1195);
return x_1197;
}
}
else
{
lean_object* x_1198; 
lean_dec(x_1066);
lean_dec_ref(x_1065);
lean_dec(x_1064);
lean_dec_ref(x_1063);
lean_dec(x_1062);
lean_dec(x_1059);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1198 = l_Lean_Compiler_LCNF_mkReturnErased(x_1069, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1198;
}
}
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
lean_dec_ref(x_1056);
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1199 = lean_ctor_get(x_1057, 0);
lean_inc(x_1199);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 x_1200 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1200 = lean_box(0);
}
if (lean_is_scalar(x_1200)) {
 x_1201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1201 = x_1200;
}
lean_ctor_set(x_1201, 0, x_1199);
return x_1201;
}
}
case 5:
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1202 = lean_ctor_get(x_1, 0);
x_1203 = lean_st_ref_get(x_3);
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc_ref(x_1204);
lean_dec(x_1203);
lean_inc(x_1202);
x_1205 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1204, x_1202, x_122);
lean_dec_ref(x_1204);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1206 = lean_ctor_get(x_1205, 0);
lean_inc(x_1206);
lean_dec_ref(x_1205);
lean_inc(x_1206);
x_1207 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1206, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1207) == 0)
{
lean_object* x_1208; uint8_t x_1209; 
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 x_1208 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1208 = lean_box(0);
}
x_1209 = l_Lean_instBEqFVarId_beq(x_1202, x_1206);
if (x_1209 == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1210 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1210 = lean_box(0);
}
if (lean_is_scalar(x_1210)) {
 x_1211 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1211 = x_1210;
}
lean_ctor_set(x_1211, 0, x_1206);
if (lean_is_scalar(x_1208)) {
 x_1212 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1212 = x_1208;
}
lean_ctor_set(x_1212, 0, x_1211);
return x_1212;
}
else
{
lean_object* x_1213; 
lean_dec(x_1206);
if (lean_is_scalar(x_1208)) {
 x_1213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1213 = x_1208;
}
lean_ctor_set(x_1213, 0, x_1);
return x_1213;
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1206);
lean_dec_ref(x_1);
x_1214 = lean_ctor_get(x_1207, 0);
lean_inc(x_1214);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 x_1215 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1216 = x_1215;
}
lean_ctor_set(x_1216, 0, x_1214);
return x_1216;
}
}
else
{
uint8_t x_1217; lean_object* x_1218; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1217 = 0;
x_1218 = l_Lean_Compiler_LCNF_mkReturnErased(x_1217, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1218;
}
}
case 6:
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; lean_object* x_1223; size_t x_1224; size_t x_1225; uint8_t x_1226; 
lean_dec_ref(x_7);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1219 = lean_ctor_get(x_1, 0);
x_1220 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc_ref(x_1221);
lean_dec(x_1220);
x_1222 = 0;
lean_inc_ref(x_1219);
x_1223 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1222, x_1221, x_122, x_1219);
lean_dec_ref(x_1221);
x_1224 = lean_ptr_addr(x_1219);
x_1225 = lean_ptr_addr(x_1223);
x_1226 = lean_usize_dec_eq(x_1224, x_1225);
if (x_1226 == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1227 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1227 = lean_box(0);
}
if (lean_is_scalar(x_1227)) {
 x_1228 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1228 = x_1227;
}
lean_ctor_set(x_1228, 0, x_1223);
x_1229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1229, 0, x_1228);
return x_1229;
}
else
{
lean_object* x_1230; 
lean_dec_ref(x_1223);
x_1230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1230, 0, x_1);
return x_1230;
}
}
default: 
{
lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_110);
lean_dec(x_109);
x_1231 = lean_ctor_get(x_1, 0);
x_1232 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1232);
lean_inc_ref(x_1231);
x_769 = x_1231;
x_770 = x_1232;
x_771 = x_2;
x_772 = x_3;
x_773 = x_4;
x_774 = x_5;
x_775 = x_6;
x_776 = x_7;
x_777 = x_8;
goto block_817;
}
}
block_817:
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_778 = lean_ctor_get(x_769, 0);
x_779 = lean_ctor_get(x_769, 2);
x_780 = lean_ctor_get(x_769, 3);
x_781 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_778, x_772);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; uint8_t x_783; uint8_t x_784; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
lean_dec_ref(x_781);
x_783 = 0;
x_784 = lean_unbox(x_782);
if (x_784 == 0)
{
uint8_t x_785; 
x_785 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
if (x_785 == 0)
{
uint8_t x_786; 
x_786 = lean_unbox(x_782);
lean_dec(x_782);
x_81 = x_770;
x_82 = x_786;
x_83 = x_769;
x_84 = x_771;
x_85 = x_772;
x_86 = x_773;
x_87 = x_774;
x_88 = x_775;
x_89 = x_776;
x_90 = x_777;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_787; 
lean_inc_ref(x_780);
x_787 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_780, x_779);
if (x_787 == 0)
{
uint8_t x_788; 
x_788 = lean_unbox(x_782);
lean_dec(x_782);
x_81 = x_770;
x_82 = x_788;
x_83 = x_769;
x_84 = x_771;
x_85 = x_772;
x_86 = x_773;
x_87 = x_774;
x_88 = x_775;
x_89 = x_776;
x_90 = x_777;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_st_ref_get(x_772);
x_790 = lean_ctor_get(x_789, 0);
lean_inc_ref(x_790);
lean_dec(x_789);
x_791 = l_Lean_Compiler_LCNF_normFunDeclImp(x_783, x_122, x_769, x_790, x_774, x_775, x_776, x_777);
lean_dec_ref(x_790);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
lean_dec_ref(x_791);
lean_inc(x_777);
lean_inc_ref(x_776);
lean_inc(x_775);
lean_inc_ref(x_774);
x_793 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_792, x_774, x_775, x_776, x_777);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
lean_dec_ref(x_793);
x_795 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_772);
if (lean_obj_tag(x_795) == 0)
{
uint8_t x_796; 
lean_dec_ref(x_795);
x_796 = lean_unbox(x_782);
lean_dec(x_782);
x_81 = x_770;
x_82 = x_796;
x_83 = x_794;
x_84 = x_771;
x_85 = x_772;
x_86 = x_773;
x_87 = x_774;
x_88 = x_775;
x_89 = x_776;
x_90 = x_777;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_794);
lean_dec(x_782);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec_ref(x_773);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec_ref(x_770);
lean_dec_ref(x_1);
x_797 = lean_ctor_get(x_795, 0);
lean_inc(x_797);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 x_798 = x_795;
} else {
 lean_dec_ref(x_795);
 x_798 = lean_box(0);
}
if (lean_is_scalar(x_798)) {
 x_799 = lean_alloc_ctor(1, 1, 0);
} else {
 x_799 = x_798;
}
lean_ctor_set(x_799, 0, x_797);
return x_799;
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_782);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec_ref(x_773);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec_ref(x_770);
lean_dec_ref(x_1);
x_800 = lean_ctor_get(x_793, 0);
lean_inc(x_800);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 x_801 = x_793;
} else {
 lean_dec_ref(x_793);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 1, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_800);
return x_802;
}
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_782);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec_ref(x_773);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec_ref(x_770);
lean_dec_ref(x_1);
x_803 = lean_ctor_get(x_791, 0);
lean_inc(x_803);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 x_804 = x_791;
} else {
 lean_dec_ref(x_791);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 1, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_803);
return x_805;
}
}
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_st_ref_get(x_772);
x_807 = lean_ctor_get(x_806, 0);
lean_inc_ref(x_807);
lean_dec(x_806);
x_808 = l_Lean_Compiler_LCNF_normFunDeclImp(x_783, x_122, x_769, x_807, x_774, x_775, x_776, x_777);
lean_dec_ref(x_807);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; uint8_t x_810; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
lean_dec_ref(x_808);
x_810 = lean_unbox(x_782);
lean_dec(x_782);
x_49 = x_770;
x_50 = x_810;
x_51 = x_809;
x_52 = x_771;
x_53 = x_772;
x_54 = x_773;
x_55 = x_774;
x_56 = x_775;
x_57 = x_776;
x_58 = x_777;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_782);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec_ref(x_773);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec_ref(x_770);
lean_dec_ref(x_1);
x_811 = lean_ctor_get(x_808, 0);
lean_inc(x_811);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 x_812 = x_808;
} else {
 lean_dec_ref(x_808);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 1, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_811);
return x_813;
}
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec_ref(x_773);
lean_dec(x_772);
lean_dec_ref(x_771);
lean_dec_ref(x_770);
lean_dec_ref(x_769);
lean_dec_ref(x_1);
x_814 = lean_ctor_get(x_781, 0);
lean_inc(x_814);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 x_815 = x_781;
} else {
 lean_dec_ref(x_781);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 1, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_814);
return x_816;
}
}
}
}
else
{
uint8_t x_1233; 
lean_free_object(x_7);
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1233 = !lean_is_exclusive(x_138);
if (x_1233 == 0)
{
return x_138;
}
else
{
lean_object* x_1234; lean_object* x_1235; 
x_1234 = lean_ctor_get(x_138, 0);
lean_inc(x_1234);
lean_dec(x_138);
x_1235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1235, 0, x_1234);
return x_1235;
}
}
}
else
{
lean_object* x_1236; 
lean_dec(x_7);
x_1236 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 x_1237 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1237 = lean_box(0);
}
x_1287 = lean_unsigned_to_nat(1u);
x_1288 = lean_nat_add(x_109, x_1287);
lean_inc(x_110);
x_1289 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_1289, 0, x_106);
lean_ctor_set(x_1289, 1, x_107);
lean_ctor_set(x_1289, 2, x_108);
lean_ctor_set(x_1289, 3, x_1288);
lean_ctor_set(x_1289, 4, x_110);
lean_ctor_set(x_1289, 5, x_111);
lean_ctor_set(x_1289, 6, x_112);
lean_ctor_set(x_1289, 7, x_113);
lean_ctor_set(x_1289, 8, x_114);
lean_ctor_set(x_1289, 9, x_115);
lean_ctor_set(x_1289, 10, x_116);
lean_ctor_set(x_1289, 11, x_117);
lean_ctor_set(x_1289, 12, x_119);
lean_ctor_set(x_1289, 13, x_121);
lean_ctor_set_uint8(x_1289, sizeof(void*)*14, x_118);
lean_ctor_set_uint8(x_1289, sizeof(void*)*14 + 1, x_120);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; uint8_t x_1301; uint8_t x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1433; 
lean_dec(x_1237);
lean_dec(x_110);
lean_dec(x_109);
x_1290 = lean_ctor_get(x_1, 0);
x_1291 = lean_ctor_get(x_1, 1);
x_1417 = 0;
lean_inc_ref(x_1290);
x_1433 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1417, x_122, x_1290, x_3, x_6);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; uint8_t x_1468; 
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
lean_dec_ref(x_1433);
lean_inc(x_1434);
lean_inc_ref(x_1290);
x_1468 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1417, x_1290, x_1434);
if (x_1468 == 0)
{
goto block_1467;
}
else
{
if (x_122 == 0)
{
x_1435 = x_2;
x_1436 = x_3;
x_1437 = x_4;
x_1438 = x_5;
x_1439 = x_6;
x_1440 = x_1289;
x_1441 = x_8;
x_1442 = lean_box(0);
goto block_1462;
}
else
{
goto block_1467;
}
}
block_1462:
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
x_1443 = lean_ctor_get(x_1434, 2);
x_1444 = lean_ctor_get(x_1434, 3);
lean_inc(x_1441);
lean_inc_ref(x_1440);
lean_inc(x_1439);
lean_inc_ref(x_1438);
lean_inc_ref(x_1437);
lean_inc(x_1444);
x_1445 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_1444, x_1435, x_1437, x_1438, x_1439, x_1440, x_1441);
if (lean_obj_tag(x_1445) == 0)
{
lean_object* x_1446; 
x_1446 = lean_ctor_get(x_1445, 0);
lean_inc(x_1446);
lean_dec_ref(x_1445);
if (lean_obj_tag(x_1446) == 1)
{
lean_object* x_1447; lean_object* x_1448; 
x_1447 = lean_ctor_get(x_1446, 0);
lean_inc(x_1447);
lean_dec_ref(x_1446);
x_1448 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1436);
if (lean_obj_tag(x_1448) == 0)
{
lean_object* x_1449; 
lean_dec_ref(x_1448);
x_1449 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_1417, x_1434, x_1447, x_1439);
if (lean_obj_tag(x_1449) == 0)
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; 
x_1450 = lean_ctor_get(x_1449, 0);
lean_inc(x_1450);
lean_dec_ref(x_1449);
x_1451 = lean_ctor_get(x_1450, 2);
lean_inc_ref(x_1451);
x_1452 = lean_ctor_get(x_1450, 3);
lean_inc(x_1452);
x_1418 = x_1450;
x_1419 = x_1451;
x_1420 = x_1452;
x_1421 = x_1435;
x_1422 = x_1436;
x_1423 = x_1437;
x_1424 = x_1438;
x_1425 = x_1439;
x_1426 = x_1440;
x_1427 = x_1441;
x_1428 = lean_box(0);
goto block_1432;
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
lean_dec(x_1441);
lean_dec_ref(x_1440);
lean_dec(x_1439);
lean_dec_ref(x_1438);
lean_dec_ref(x_1437);
lean_dec(x_1436);
lean_dec_ref(x_1435);
lean_dec_ref(x_1);
x_1453 = lean_ctor_get(x_1449, 0);
lean_inc(x_1453);
if (lean_is_exclusive(x_1449)) {
 lean_ctor_release(x_1449, 0);
 x_1454 = x_1449;
} else {
 lean_dec_ref(x_1449);
 x_1454 = lean_box(0);
}
if (lean_is_scalar(x_1454)) {
 x_1455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1455 = x_1454;
}
lean_ctor_set(x_1455, 0, x_1453);
return x_1455;
}
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_1447);
lean_dec(x_1441);
lean_dec_ref(x_1440);
lean_dec(x_1439);
lean_dec_ref(x_1438);
lean_dec_ref(x_1437);
lean_dec(x_1436);
lean_dec_ref(x_1435);
lean_dec(x_1434);
lean_dec_ref(x_1);
x_1456 = lean_ctor_get(x_1448, 0);
lean_inc(x_1456);
if (lean_is_exclusive(x_1448)) {
 lean_ctor_release(x_1448, 0);
 x_1457 = x_1448;
} else {
 lean_dec_ref(x_1448);
 x_1457 = lean_box(0);
}
if (lean_is_scalar(x_1457)) {
 x_1458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1458 = x_1457;
}
lean_ctor_set(x_1458, 0, x_1456);
return x_1458;
}
}
else
{
lean_dec(x_1446);
lean_inc(x_1444);
lean_inc_ref(x_1443);
x_1418 = x_1434;
x_1419 = x_1443;
x_1420 = x_1444;
x_1421 = x_1435;
x_1422 = x_1436;
x_1423 = x_1437;
x_1424 = x_1438;
x_1425 = x_1439;
x_1426 = x_1440;
x_1427 = x_1441;
x_1428 = lean_box(0);
goto block_1432;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1441);
lean_dec_ref(x_1440);
lean_dec(x_1439);
lean_dec_ref(x_1438);
lean_dec_ref(x_1437);
lean_dec(x_1436);
lean_dec_ref(x_1435);
lean_dec(x_1434);
lean_dec_ref(x_1);
x_1459 = lean_ctor_get(x_1445, 0);
lean_inc(x_1459);
if (lean_is_exclusive(x_1445)) {
 lean_ctor_release(x_1445, 0);
 x_1460 = x_1445;
} else {
 lean_dec_ref(x_1445);
 x_1460 = lean_box(0);
}
if (lean_is_scalar(x_1460)) {
 x_1461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1461 = x_1460;
}
lean_ctor_set(x_1461, 0, x_1459);
return x_1461;
}
}
block_1467:
{
lean_object* x_1463; 
x_1463 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_1463) == 0)
{
lean_dec_ref(x_1463);
x_1435 = x_2;
x_1436 = x_3;
x_1437 = x_4;
x_1438 = x_5;
x_1439 = x_6;
x_1440 = x_1289;
x_1441 = x_8;
x_1442 = lean_box(0);
goto block_1462;
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
lean_dec(x_1434);
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 x_1465 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1465 = lean_box(0);
}
if (lean_is_scalar(x_1465)) {
 x_1466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1466 = x_1465;
}
lean_ctor_set(x_1466, 0, x_1464);
return x_1466;
}
}
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1469 = lean_ctor_get(x_1433, 0);
lean_inc(x_1469);
if (lean_is_exclusive(x_1433)) {
 lean_ctor_release(x_1433, 0);
 x_1470 = x_1433;
} else {
 lean_dec_ref(x_1433);
 x_1470 = lean_box(0);
}
if (lean_is_scalar(x_1470)) {
 x_1471 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1471 = x_1470;
}
lean_ctor_set(x_1471, 0, x_1469);
return x_1471;
}
block_1416:
{
if (x_1301 == 0)
{
lean_object* x_1302; 
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1294);
x_1302 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_1294, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
lean_dec_ref(x_1302);
if (lean_obj_tag(x_1303) == 1)
{
lean_object* x_1304; lean_object* x_1305; 
lean_dec_ref(x_1294);
lean_inc_ref(x_1291);
lean_dec_ref(x_1);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
lean_dec_ref(x_1303);
x_1305 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1297);
if (lean_obj_tag(x_1305) == 0)
{
lean_object* x_1306; 
lean_dec_ref(x_1305);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1300);
lean_inc(x_1297);
lean_inc_ref(x_1296);
x_1306 = l_Lean_Compiler_LCNF_Simp_simp(x_1291, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
lean_dec_ref(x_1306);
x_1308 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1304, x_1307, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
lean_dec(x_1299);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1295);
lean_dec_ref(x_1300);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1304);
return x_1308;
}
else
{
lean_dec(x_1304);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
return x_1306;
}
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1304);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1309 = lean_ctor_get(x_1305, 0);
lean_inc(x_1309);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 x_1310 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1310 = lean_box(0);
}
if (lean_is_scalar(x_1310)) {
 x_1311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1311 = x_1310;
}
lean_ctor_set(x_1311, 0, x_1309);
return x_1311;
}
}
else
{
lean_object* x_1312; 
lean_dec(x_1303);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1294);
x_1312 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1294, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec_ref(x_1312);
if (lean_obj_tag(x_1313) == 1)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
lean_dec_ref(x_1294);
lean_inc_ref(x_1291);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1314 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1314 = lean_box(0);
}
x_1315 = lean_ctor_get(x_1313, 0);
lean_inc(x_1315);
lean_dec_ref(x_1313);
if (lean_is_scalar(x_1314)) {
 x_1316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1316 = x_1314;
 lean_ctor_set_tag(x_1316, 1);
}
lean_ctor_set(x_1316, 0, x_1315);
lean_ctor_set(x_1316, 1, x_1291);
x_1 = x_1316;
x_2 = x_1296;
x_3 = x_1297;
x_4 = x_1300;
x_5 = x_1295;
x_6 = x_1292;
x_7 = x_1293;
x_8 = x_1299;
goto _start;
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_1313);
x_1318 = lean_ctor_get(x_1294, 0);
x_1319 = lean_ctor_get(x_1294, 3);
x_1320 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1319);
if (lean_obj_tag(x_1320) == 0)
{
lean_object* x_1321; 
x_1321 = lean_ctor_get(x_1320, 0);
lean_inc(x_1321);
lean_dec_ref(x_1320);
if (lean_obj_tag(x_1321) == 1)
{
lean_object* x_1322; lean_object* x_1323; 
lean_inc_ref(x_1291);
lean_dec_ref(x_1);
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
lean_dec_ref(x_1321);
lean_inc(x_1318);
x_1323 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1318, x_1322, x_1297, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; 
lean_dec_ref(x_1323);
x_1324 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1294, x_1297, x_1292);
lean_dec_ref(x_1294);
if (lean_obj_tag(x_1324) == 0)
{
lean_dec_ref(x_1324);
x_1 = x_1291;
x_2 = x_1296;
x_3 = x_1297;
x_4 = x_1300;
x_5 = x_1295;
x_6 = x_1292;
x_7 = x_1293;
x_8 = x_1299;
goto _start;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1326 = lean_ctor_get(x_1324, 0);
lean_inc(x_1326);
if (lean_is_exclusive(x_1324)) {
 lean_ctor_release(x_1324, 0);
 x_1327 = x_1324;
} else {
 lean_dec_ref(x_1324);
 x_1327 = lean_box(0);
}
if (lean_is_scalar(x_1327)) {
 x_1328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1328 = x_1327;
}
lean_ctor_set(x_1328, 0, x_1326);
return x_1328;
}
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1329 = lean_ctor_get(x_1323, 0);
lean_inc(x_1329);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 x_1330 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1330 = lean_box(0);
}
if (lean_is_scalar(x_1330)) {
 x_1331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1331 = x_1330;
}
lean_ctor_set(x_1331, 0, x_1329);
return x_1331;
}
}
else
{
lean_object* x_1332; 
lean_dec(x_1321);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1300);
lean_inc(x_1297);
lean_inc_ref(x_1296);
lean_inc_ref(x_1291);
lean_inc_ref(x_1294);
x_1332 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1294, x_1291, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; 
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
lean_dec_ref(x_1332);
if (lean_obj_tag(x_1333) == 1)
{
lean_object* x_1334; lean_object* x_1335; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec_ref(x_1);
x_1334 = lean_ctor_get(x_1333, 0);
lean_inc(x_1334);
lean_dec_ref(x_1333);
x_1335 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1294, x_1297, x_1292);
lean_dec(x_1292);
lean_dec(x_1297);
lean_dec_ref(x_1294);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; 
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 x_1336 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1336 = lean_box(0);
}
if (lean_is_scalar(x_1336)) {
 x_1337 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1337 = x_1336;
}
lean_ctor_set(x_1337, 0, x_1334);
return x_1337;
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
lean_dec(x_1334);
x_1338 = lean_ctor_get(x_1335, 0);
lean_inc(x_1338);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 x_1339 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_1338);
return x_1340;
}
}
else
{
lean_object* x_1341; 
lean_dec(x_1333);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1300);
lean_inc(x_1297);
lean_inc_ref(x_1296);
lean_inc(x_1319);
x_1341 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_1319, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1341) == 0)
{
lean_object* x_1342; 
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
lean_dec_ref(x_1341);
if (lean_obj_tag(x_1342) == 1)
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
lean_inc_ref(x_1291);
lean_dec_ref(x_1);
x_1343 = lean_ctor_get(x_1342, 0);
lean_inc(x_1343);
lean_dec_ref(x_1342);
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1343, 1);
lean_inc(x_1345);
lean_dec(x_1343);
lean_inc(x_1318);
x_1346 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_1318, x_1345, x_1297, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1346) == 0)
{
lean_object* x_1347; 
lean_dec_ref(x_1346);
x_1347 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1294, x_1297, x_1292);
lean_dec_ref(x_1294);
if (lean_obj_tag(x_1347) == 0)
{
lean_object* x_1348; 
lean_dec_ref(x_1347);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1300);
lean_inc(x_1297);
lean_inc_ref(x_1296);
x_1348 = l_Lean_Compiler_LCNF_Simp_simp(x_1291, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1348) == 0)
{
lean_object* x_1349; lean_object* x_1350; 
x_1349 = lean_ctor_get(x_1348, 0);
lean_inc(x_1349);
lean_dec_ref(x_1348);
x_1350 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1344, x_1349, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
lean_dec(x_1299);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1295);
lean_dec_ref(x_1300);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec(x_1344);
return x_1350;
}
else
{
lean_dec(x_1344);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
return x_1348;
}
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_1344);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1351 = lean_ctor_get(x_1347, 0);
lean_inc(x_1351);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 x_1352 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1352 = lean_box(0);
}
if (lean_is_scalar(x_1352)) {
 x_1353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1353 = x_1352;
}
lean_ctor_set(x_1353, 0, x_1351);
return x_1353;
}
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
lean_dec(x_1344);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1354 = lean_ctor_get(x_1346, 0);
lean_inc(x_1354);
if (lean_is_exclusive(x_1346)) {
 lean_ctor_release(x_1346, 0);
 x_1355 = x_1346;
} else {
 lean_dec_ref(x_1346);
 x_1355 = lean_box(0);
}
if (lean_is_scalar(x_1355)) {
 x_1356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1356 = x_1355;
}
lean_ctor_set(x_1356, 0, x_1354);
return x_1356;
}
}
else
{
lean_object* x_1357; 
lean_dec(x_1342);
lean_inc(x_1299);
lean_inc_ref(x_1293);
lean_inc(x_1292);
lean_inc_ref(x_1295);
lean_inc_ref(x_1300);
lean_inc(x_1297);
lean_inc_ref(x_1296);
lean_inc_ref(x_1291);
x_1357 = l_Lean_Compiler_LCNF_Simp_simp(x_1291, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
if (lean_obj_tag(x_1357) == 0)
{
lean_object* x_1358; lean_object* x_1359; 
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
lean_dec_ref(x_1357);
x_1359 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_1318, x_1297);
if (lean_obj_tag(x_1359) == 0)
{
lean_object* x_1360; uint8_t x_1361; 
x_1360 = lean_ctor_get(x_1359, 0);
lean_inc(x_1360);
lean_dec_ref(x_1359);
x_1361 = lean_unbox(x_1360);
lean_dec(x_1360);
if (x_1361 == 0)
{
lean_object* x_1362; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec_ref(x_1);
x_1362 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1294, x_1297, x_1292);
lean_dec(x_1292);
lean_dec(x_1297);
lean_dec_ref(x_1294);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; 
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 x_1363 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1363 = lean_box(0);
}
if (lean_is_scalar(x_1363)) {
 x_1364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1364 = x_1363;
}
lean_ctor_set(x_1364, 0, x_1358);
return x_1364;
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
lean_dec(x_1358);
x_1365 = lean_ctor_get(x_1362, 0);
lean_inc(x_1365);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 x_1366 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1366 = lean_box(0);
}
if (lean_is_scalar(x_1366)) {
 x_1367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1367 = x_1366;
}
lean_ctor_set(x_1367, 0, x_1365);
return x_1367;
}
}
else
{
lean_object* x_1368; 
lean_inc_ref(x_1294);
x_1368 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_1294, x_1296, x_1297, x_1300, x_1295, x_1292, x_1293, x_1299);
lean_dec(x_1299);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1295);
lean_dec_ref(x_1300);
lean_dec(x_1297);
lean_dec_ref(x_1296);
if (lean_obj_tag(x_1368) == 0)
{
size_t x_1369; size_t x_1370; uint8_t x_1371; 
lean_dec_ref(x_1368);
x_1369 = lean_ptr_addr(x_1291);
x_1370 = lean_ptr_addr(x_1358);
x_1371 = lean_usize_dec_eq(x_1369, x_1370);
if (x_1371 == 0)
{
x_98 = x_1358;
x_99 = x_1294;
x_100 = lean_box(0);
x_101 = x_1371;
goto block_105;
}
else
{
size_t x_1372; size_t x_1373; uint8_t x_1374; 
x_1372 = lean_ptr_addr(x_1290);
x_1373 = lean_ptr_addr(x_1294);
x_1374 = lean_usize_dec_eq(x_1372, x_1373);
x_98 = x_1358;
x_99 = x_1294;
x_100 = lean_box(0);
x_101 = x_1374;
goto block_105;
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_1358);
lean_dec_ref(x_1294);
lean_dec_ref(x_1);
x_1375 = lean_ctor_get(x_1368, 0);
lean_inc(x_1375);
if (lean_is_exclusive(x_1368)) {
 lean_ctor_release(x_1368, 0);
 x_1376 = x_1368;
} else {
 lean_dec_ref(x_1368);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1375);
return x_1377;
}
}
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
lean_dec(x_1358);
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1378 = lean_ctor_get(x_1359, 0);
lean_inc(x_1378);
if (lean_is_exclusive(x_1359)) {
 lean_ctor_release(x_1359, 0);
 x_1379 = x_1359;
} else {
 lean_dec_ref(x_1359);
 x_1379 = lean_box(0);
}
if (lean_is_scalar(x_1379)) {
 x_1380 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1380 = x_1379;
}
lean_ctor_set(x_1380, 0, x_1378);
return x_1380;
}
}
else
{
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
return x_1357;
}
}
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1381 = lean_ctor_get(x_1341, 0);
lean_inc(x_1381);
if (lean_is_exclusive(x_1341)) {
 lean_ctor_release(x_1341, 0);
 x_1382 = x_1341;
} else {
 lean_dec_ref(x_1341);
 x_1382 = lean_box(0);
}
if (lean_is_scalar(x_1382)) {
 x_1383 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1383 = x_1382;
}
lean_ctor_set(x_1383, 0, x_1381);
return x_1383;
}
}
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1384 = lean_ctor_get(x_1332, 0);
lean_inc(x_1384);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 x_1385 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1385 = lean_box(0);
}
if (lean_is_scalar(x_1385)) {
 x_1386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1386 = x_1385;
}
lean_ctor_set(x_1386, 0, x_1384);
return x_1386;
}
}
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1387 = lean_ctor_get(x_1320, 0);
lean_inc(x_1387);
if (lean_is_exclusive(x_1320)) {
 lean_ctor_release(x_1320, 0);
 x_1388 = x_1320;
} else {
 lean_dec_ref(x_1320);
 x_1388 = lean_box(0);
}
if (lean_is_scalar(x_1388)) {
 x_1389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1389 = x_1388;
}
lean_ctor_set(x_1389, 0, x_1387);
return x_1389;
}
}
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1390 = lean_ctor_get(x_1312, 0);
lean_inc(x_1390);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 x_1391 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1391 = lean_box(0);
}
if (lean_is_scalar(x_1391)) {
 x_1392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1392 = x_1391;
}
lean_ctor_set(x_1392, 0, x_1390);
return x_1392;
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1294);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1);
x_1393 = lean_ctor_get(x_1302, 0);
lean_inc(x_1393);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 x_1394 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1394 = lean_box(0);
}
if (lean_is_scalar(x_1394)) {
 x_1395 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1395 = x_1394;
}
lean_ctor_set(x_1395, 0, x_1393);
return x_1395;
}
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; uint8_t x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
lean_inc_ref(x_1291);
lean_dec_ref(x_1);
x_1396 = lean_st_ref_take(x_1297);
x_1397 = lean_ctor_get(x_1294, 0);
x_1398 = lean_ctor_get(x_1396, 0);
lean_inc_ref(x_1398);
x_1399 = lean_ctor_get(x_1396, 1);
lean_inc_ref(x_1399);
x_1400 = lean_ctor_get(x_1396, 2);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1396, 3);
lean_inc_ref(x_1401);
x_1402 = lean_ctor_get_uint8(x_1396, sizeof(void*)*7);
x_1403 = lean_ctor_get(x_1396, 4);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1396, 5);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1396, 6);
lean_inc(x_1405);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 lean_ctor_release(x_1396, 2);
 lean_ctor_release(x_1396, 3);
 lean_ctor_release(x_1396, 4);
 lean_ctor_release(x_1396, 5);
 lean_ctor_release(x_1396, 6);
 x_1406 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1406 = lean_box(0);
}
x_1407 = lean_box(0);
lean_inc(x_1397);
x_1408 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1398, x_1397, x_1407);
if (lean_is_scalar(x_1406)) {
 x_1409 = lean_alloc_ctor(0, 7, 1);
} else {
 x_1409 = x_1406;
}
lean_ctor_set(x_1409, 0, x_1408);
lean_ctor_set(x_1409, 1, x_1399);
lean_ctor_set(x_1409, 2, x_1400);
lean_ctor_set(x_1409, 3, x_1401);
lean_ctor_set(x_1409, 4, x_1403);
lean_ctor_set(x_1409, 5, x_1404);
lean_ctor_set(x_1409, 6, x_1405);
lean_ctor_set_uint8(x_1409, sizeof(void*)*7, x_1402);
x_1410 = lean_st_ref_set(x_1297, x_1409);
x_1411 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1294, x_1297, x_1292);
lean_dec_ref(x_1294);
if (lean_obj_tag(x_1411) == 0)
{
lean_dec_ref(x_1411);
x_1 = x_1291;
x_2 = x_1296;
x_3 = x_1297;
x_4 = x_1300;
x_5 = x_1295;
x_6 = x_1292;
x_7 = x_1293;
x_8 = x_1299;
goto _start;
}
else
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
lean_dec_ref(x_1300);
lean_dec(x_1299);
lean_dec(x_1297);
lean_dec_ref(x_1296);
lean_dec_ref(x_1295);
lean_dec_ref(x_1293);
lean_dec(x_1292);
lean_dec_ref(x_1291);
x_1413 = lean_ctor_get(x_1411, 0);
lean_inc(x_1413);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 x_1414 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1414 = lean_box(0);
}
if (lean_is_scalar(x_1414)) {
 x_1415 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1415 = x_1414;
}
lean_ctor_set(x_1415, 0, x_1413);
return x_1415;
}
}
}
block_1432:
{
uint8_t x_1429; 
x_1429 = l_Lean_Expr_isErased(x_1419);
lean_dec_ref(x_1419);
if (x_1429 == 0)
{
lean_dec(x_1420);
x_1292 = x_1425;
x_1293 = x_1426;
x_1294 = x_1418;
x_1295 = x_1424;
x_1296 = x_1421;
x_1297 = x_1422;
x_1298 = lean_box(0);
x_1299 = x_1427;
x_1300 = x_1423;
x_1301 = x_122;
goto block_1416;
}
else
{
lean_object* x_1430; uint8_t x_1431; 
x_1430 = lean_box(1);
x_1431 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1417, x_1420, x_1430);
if (x_1431 == 0)
{
x_1292 = x_1425;
x_1293 = x_1426;
x_1294 = x_1418;
x_1295 = x_1424;
x_1296 = x_1421;
x_1297 = x_1422;
x_1298 = lean_box(0);
x_1299 = x_1427;
x_1300 = x_1423;
x_1301 = x_1429;
goto block_1416;
}
else
{
x_1292 = x_1425;
x_1293 = x_1426;
x_1294 = x_1418;
x_1295 = x_1424;
x_1296 = x_1421;
x_1297 = x_1422;
x_1298 = lean_box(0);
x_1299 = x_1427;
x_1300 = x_1423;
x_1301 = x_122;
goto block_1416;
}
}
}
}
case 3:
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; uint8_t x_1476; lean_object* x_1477; 
lean_dec(x_1237);
lean_dec(x_110);
lean_dec(x_109);
x_1472 = lean_ctor_get(x_1, 0);
x_1473 = lean_ctor_get(x_1, 1);
x_1474 = lean_st_ref_get(x_3);
x_1475 = lean_ctor_get(x_1474, 0);
lean_inc_ref(x_1475);
lean_dec(x_1474);
x_1476 = 0;
lean_inc(x_1472);
x_1477 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1475, x_1472, x_122);
lean_dec_ref(x_1475);
if (lean_obj_tag(x_1477) == 0)
{
lean_object* x_1478; lean_object* x_1479; 
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
lean_dec_ref(x_1477);
lean_inc_ref(x_1473);
x_1479 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1476, x_122, x_1473, x_3);
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; uint8_t x_1483; lean_object* x_1489; lean_object* x_1495; lean_object* x_1500; 
x_1480 = lean_ctor_get(x_1479, 0);
lean_inc(x_1480);
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 x_1481 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1481 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1289);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1480);
x_1500 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1478, x_1480, x_2, x_3, x_4, x_5, x_6, x_1289, x_8);
if (lean_obj_tag(x_1500) == 0)
{
lean_object* x_1501; 
x_1501 = lean_ctor_get(x_1500, 0);
lean_inc(x_1501);
lean_dec_ref(x_1500);
if (lean_obj_tag(x_1501) == 1)
{
lean_object* x_1502; 
lean_dec(x_1481);
lean_dec(x_1480);
lean_dec(x_1478);
lean_dec_ref(x_1);
x_1502 = lean_ctor_get(x_1501, 0);
lean_inc(x_1502);
lean_dec_ref(x_1501);
x_1 = x_1502;
x_7 = x_1289;
goto _start;
}
else
{
lean_object* x_1504; 
lean_dec(x_1501);
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_1478);
x_1504 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1478, x_3);
if (lean_obj_tag(x_1504) == 0)
{
lean_object* x_1505; lean_object* x_1506; uint8_t x_1507; 
lean_dec_ref(x_1504);
x_1505 = lean_unsigned_to_nat(0u);
x_1506 = lean_array_get_size(x_1480);
x_1507 = lean_nat_dec_lt(x_1505, x_1506);
if (x_1507 == 0)
{
lean_dec(x_3);
x_1489 = lean_box(0);
goto block_1494;
}
else
{
lean_object* x_1508; uint8_t x_1509; 
x_1508 = lean_box(0);
x_1509 = lean_nat_dec_le(x_1506, x_1506);
if (x_1509 == 0)
{
if (x_1507 == 0)
{
lean_dec(x_3);
x_1489 = lean_box(0);
goto block_1494;
}
else
{
size_t x_1510; size_t x_1511; lean_object* x_1512; 
x_1510 = 0;
x_1511 = lean_usize_of_nat(x_1506);
x_1512 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1480, x_1510, x_1511, x_1508, x_3);
lean_dec(x_3);
x_1495 = x_1512;
goto block_1499;
}
}
else
{
size_t x_1513; size_t x_1514; lean_object* x_1515; 
x_1513 = 0;
x_1514 = lean_usize_of_nat(x_1506);
x_1515 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1480, x_1513, x_1514, x_1508, x_3);
lean_dec(x_3);
x_1495 = x_1515;
goto block_1499;
}
}
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
lean_dec(x_1481);
lean_dec(x_1480);
lean_dec(x_1478);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1516 = lean_ctor_get(x_1504, 0);
lean_inc(x_1516);
if (lean_is_exclusive(x_1504)) {
 lean_ctor_release(x_1504, 0);
 x_1517 = x_1504;
} else {
 lean_dec_ref(x_1504);
 x_1517 = lean_box(0);
}
if (lean_is_scalar(x_1517)) {
 x_1518 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1518 = x_1517;
}
lean_ctor_set(x_1518, 0, x_1516);
return x_1518;
}
}
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_1481);
lean_dec(x_1480);
lean_dec(x_1478);
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1519 = lean_ctor_get(x_1500, 0);
lean_inc(x_1519);
if (lean_is_exclusive(x_1500)) {
 lean_ctor_release(x_1500, 0);
 x_1520 = x_1500;
} else {
 lean_dec_ref(x_1500);
 x_1520 = lean_box(0);
}
if (lean_is_scalar(x_1520)) {
 x_1521 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1521 = x_1520;
}
lean_ctor_set(x_1521, 0, x_1519);
return x_1521;
}
block_1488:
{
if (x_1483 == 0)
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_1484 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1484 = lean_box(0);
}
if (lean_is_scalar(x_1484)) {
 x_1485 = lean_alloc_ctor(3, 2, 0);
} else {
 x_1485 = x_1484;
}
lean_ctor_set(x_1485, 0, x_1478);
lean_ctor_set(x_1485, 1, x_1480);
if (lean_is_scalar(x_1481)) {
 x_1486 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1486 = x_1481;
}
lean_ctor_set(x_1486, 0, x_1485);
return x_1486;
}
else
{
lean_object* x_1487; 
lean_dec(x_1480);
lean_dec(x_1478);
if (lean_is_scalar(x_1481)) {
 x_1487 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1487 = x_1481;
}
lean_ctor_set(x_1487, 0, x_1);
return x_1487;
}
}
block_1494:
{
uint8_t x_1490; 
x_1490 = l_Lean_instBEqFVarId_beq(x_1472, x_1478);
if (x_1490 == 0)
{
x_1482 = lean_box(0);
x_1483 = x_1490;
goto block_1488;
}
else
{
size_t x_1491; size_t x_1492; uint8_t x_1493; 
x_1491 = lean_ptr_addr(x_1473);
x_1492 = lean_ptr_addr(x_1480);
x_1493 = lean_usize_dec_eq(x_1491, x_1492);
x_1482 = lean_box(0);
x_1483 = x_1493;
goto block_1488;
}
}
block_1499:
{
if (lean_obj_tag(x_1495) == 0)
{
lean_dec_ref(x_1495);
x_1489 = lean_box(0);
goto block_1494;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
lean_dec(x_1481);
lean_dec(x_1480);
lean_dec(x_1478);
lean_dec_ref(x_1);
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
if (lean_is_exclusive(x_1495)) {
 lean_ctor_release(x_1495, 0);
 x_1497 = x_1495;
} else {
 lean_dec_ref(x_1495);
 x_1497 = lean_box(0);
}
if (lean_is_scalar(x_1497)) {
 x_1498 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1498 = x_1497;
}
lean_ctor_set(x_1498, 0, x_1496);
return x_1498;
}
}
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
lean_dec(x_1478);
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1522 = lean_ctor_get(x_1479, 0);
lean_inc(x_1522);
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 x_1523 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1523 = lean_box(0);
}
if (lean_is_scalar(x_1523)) {
 x_1524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1524 = x_1523;
}
lean_ctor_set(x_1524, 0, x_1522);
return x_1524;
}
}
else
{
lean_object* x_1525; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1525 = l_Lean_Compiler_LCNF_mkReturnErased(x_1476, x_5, x_6, x_1289, x_8);
lean_dec(x_8);
lean_dec_ref(x_1289);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1525;
}
}
case 4:
{
lean_object* x_1526; lean_object* x_1527; 
lean_dec(x_1237);
x_1526 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_1526);
lean_inc(x_8);
lean_inc_ref(x_1289);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1526);
x_1527 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1526, x_2, x_3, x_4, x_5, x_6, x_1289, x_8);
if (lean_obj_tag(x_1527) == 0)
{
lean_object* x_1528; lean_object* x_1529; 
x_1528 = lean_ctor_get(x_1527, 0);
lean_inc(x_1528);
if (lean_is_exclusive(x_1527)) {
 lean_ctor_release(x_1527, 0);
 x_1529 = x_1527;
} else {
 lean_dec_ref(x_1527);
 x_1529 = lean_box(0);
}
if (lean_obj_tag(x_1528) == 1)
{
lean_object* x_1530; lean_object* x_1531; 
lean_dec_ref(x_1526);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1530 = lean_ctor_get(x_1528, 0);
lean_inc(x_1530);
lean_dec_ref(x_1528);
if (lean_is_scalar(x_1529)) {
 x_1531 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1531 = x_1529;
}
lean_ctor_set(x_1531, 0, x_1530);
return x_1531;
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; lean_object* x_1540; 
lean_dec(x_1528);
x_1532 = lean_ctor_get(x_1526, 0);
lean_inc(x_1532);
x_1533 = lean_ctor_get(x_1526, 1);
lean_inc_ref(x_1533);
x_1534 = lean_ctor_get(x_1526, 2);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1526, 3);
lean_inc_ref(x_1535);
if (lean_is_exclusive(x_1526)) {
 lean_ctor_release(x_1526, 0);
 lean_ctor_release(x_1526, 1);
 lean_ctor_release(x_1526, 2);
 lean_ctor_release(x_1526, 3);
 x_1536 = x_1526;
} else {
 lean_dec_ref(x_1526);
 x_1536 = lean_box(0);
}
x_1537 = lean_st_ref_get(x_3);
x_1538 = lean_ctor_get(x_1537, 0);
lean_inc_ref(x_1538);
lean_dec(x_1537);
x_1539 = 0;
lean_inc(x_1534);
x_1540 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1538, x_1534, x_122);
lean_dec_ref(x_1538);
if (lean_obj_tag(x_1540) == 0)
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; 
x_1541 = lean_ctor_get(x_1540, 0);
lean_inc(x_1541);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 x_1542 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1542 = lean_box(0);
}
x_1543 = lean_st_ref_get(x_3);
x_1544 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_1289);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1535);
lean_inc(x_1541);
x_1545 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1541, x_109, x_110, x_1544, x_1535, x_2, x_3, x_4, x_5, x_6, x_1289, x_8);
if (lean_obj_tag(x_1545) == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; 
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 x_1547 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1547 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_1289);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_1548 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_1546, x_2, x_3, x_4, x_5, x_6, x_1289, x_8);
if (lean_obj_tag(x_1548) == 0)
{
lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1563; lean_object* x_1564; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1586; lean_object* x_1591; uint8_t x_1592; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1618; uint8_t x_1619; 
x_1549 = lean_ctor_get(x_1548, 0);
lean_inc(x_1549);
if (lean_is_exclusive(x_1548)) {
 lean_ctor_release(x_1548, 0);
 x_1550 = x_1548;
} else {
 lean_dec_ref(x_1548);
 x_1550 = lean_box(0);
}
x_1551 = lean_ctor_get(x_1543, 0);
lean_inc_ref(x_1551);
lean_dec(x_1543);
lean_inc_ref(x_1533);
x_1552 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1539, x_1551, x_122, x_1533);
lean_dec_ref(x_1551);
x_1618 = lean_array_get_size(x_1549);
x_1619 = lean_nat_dec_eq(x_1618, x_1287);
if (x_1619 == 0)
{
lean_dec(x_1529);
x_1596 = x_3;
x_1597 = x_5;
x_1598 = x_6;
x_1599 = x_1289;
x_1600 = x_8;
x_1601 = lean_box(0);
goto block_1617;
}
else
{
lean_object* x_1620; 
x_1620 = lean_array_fget_borrowed(x_1549, x_1544);
if (lean_obj_tag(x_1620) == 0)
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1631; lean_object* x_1636; lean_object* x_1637; uint8_t x_1648; lean_object* x_1649; uint8_t x_1651; 
lean_dec(x_1529);
x_1621 = lean_ctor_get(x_1620, 1);
x_1622 = lean_ctor_get(x_1620, 2);
x_1636 = lean_array_get_size(x_1621);
x_1651 = lean_nat_dec_lt(x_1544, x_1636);
if (x_1651 == 0)
{
x_1648 = x_122;
x_1649 = lean_box(0);
goto block_1650;
}
else
{
if (x_1651 == 0)
{
x_1648 = x_122;
x_1649 = lean_box(0);
goto block_1650;
}
else
{
size_t x_1652; size_t x_1653; lean_object* x_1654; 
x_1652 = 0;
x_1653 = lean_usize_of_nat(x_1636);
x_1654 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1621, x_1652, x_1653, x_3);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; uint8_t x_1656; 
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
lean_dec_ref(x_1654);
x_1656 = lean_unbox(x_1655);
lean_dec(x_1655);
x_1648 = x_1656;
x_1649 = lean_box(0);
goto block_1650;
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1657 = lean_ctor_get(x_1654, 0);
lean_inc(x_1657);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 x_1658 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1658 = lean_box(0);
}
if (lean_is_scalar(x_1658)) {
 x_1659 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1659 = x_1658;
}
lean_ctor_set(x_1659, 0, x_1657);
return x_1659;
}
}
}
block_1630:
{
lean_object* x_1624; 
x_1624 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1624) == 0)
{
lean_object* x_1625; lean_object* x_1626; 
if (lean_is_exclusive(x_1624)) {
 lean_ctor_release(x_1624, 0);
 x_1625 = x_1624;
} else {
 lean_dec_ref(x_1624);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1625)) {
 x_1626 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1626 = x_1625;
}
lean_ctor_set(x_1626, 0, x_1622);
return x_1626;
}
else
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
lean_dec_ref(x_1622);
x_1627 = lean_ctor_get(x_1624, 0);
lean_inc(x_1627);
if (lean_is_exclusive(x_1624)) {
 lean_ctor_release(x_1624, 0);
 x_1628 = x_1624;
} else {
 lean_dec_ref(x_1624);
 x_1628 = lean_box(0);
}
if (lean_is_scalar(x_1628)) {
 x_1629 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1629 = x_1628;
}
lean_ctor_set(x_1629, 0, x_1627);
return x_1629;
}
}
block_1635:
{
if (lean_obj_tag(x_1631) == 0)
{
lean_dec_ref(x_1631);
x_1623 = lean_box(0);
goto block_1630;
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
lean_dec_ref(x_1622);
lean_dec(x_3);
x_1632 = lean_ctor_get(x_1631, 0);
lean_inc(x_1632);
if (lean_is_exclusive(x_1631)) {
 lean_ctor_release(x_1631, 0);
 x_1633 = x_1631;
} else {
 lean_dec_ref(x_1631);
 x_1633 = lean_box(0);
}
if (lean_is_scalar(x_1633)) {
 x_1634 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1634 = x_1633;
}
lean_ctor_set(x_1634, 0, x_1632);
return x_1634;
}
}
block_1647:
{
uint8_t x_1638; 
x_1638 = lean_nat_dec_lt(x_1544, x_1636);
if (x_1638 == 0)
{
lean_dec_ref(x_1621);
lean_dec(x_6);
x_1623 = lean_box(0);
goto block_1630;
}
else
{
lean_object* x_1639; uint8_t x_1640; 
x_1639 = lean_box(0);
x_1640 = lean_nat_dec_le(x_1636, x_1636);
if (x_1640 == 0)
{
if (x_1638 == 0)
{
lean_dec_ref(x_1621);
lean_dec(x_6);
x_1623 = lean_box(0);
goto block_1630;
}
else
{
size_t x_1641; size_t x_1642; lean_object* x_1643; 
x_1641 = 0;
x_1642 = lean_usize_of_nat(x_1636);
x_1643 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1621, x_1641, x_1642, x_1639, x_6);
lean_dec(x_6);
lean_dec_ref(x_1621);
x_1631 = x_1643;
goto block_1635;
}
}
else
{
size_t x_1644; size_t x_1645; lean_object* x_1646; 
x_1644 = 0;
x_1645 = lean_usize_of_nat(x_1636);
x_1646 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1621, x_1644, x_1645, x_1639, x_6);
lean_dec(x_6);
lean_dec_ref(x_1621);
x_1631 = x_1646;
goto block_1635;
}
}
}
block_1650:
{
if (x_1648 == 0)
{
lean_inc_ref(x_1622);
lean_inc_ref(x_1621);
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1637 = lean_box(0);
goto block_1647;
}
else
{
if (x_122 == 0)
{
x_1596 = x_3;
x_1597 = x_5;
x_1598 = x_6;
x_1599 = x_1289;
x_1600 = x_8;
x_1601 = lean_box(0);
goto block_1617;
}
else
{
lean_inc_ref(x_1622);
lean_inc_ref(x_1621);
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_1637 = lean_box(0);
goto block_1647;
}
}
}
}
else
{
lean_object* x_1660; lean_object* x_1661; 
lean_inc_ref(x_1620);
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1660 = lean_ctor_get(x_1620, 0);
lean_inc_ref(x_1660);
lean_dec_ref(x_1620);
if (lean_is_scalar(x_1529)) {
 x_1661 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1661 = x_1529;
}
lean_ctor_set(x_1661, 0, x_1660);
return x_1661;
}
}
block_1562:
{
lean_object* x_1555; 
x_1555 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1553);
lean_dec(x_1553);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 x_1556 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1556 = lean_box(0);
}
if (lean_is_scalar(x_1542)) {
 x_1557 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1557 = x_1542;
 lean_ctor_set_tag(x_1557, 6);
}
lean_ctor_set(x_1557, 0, x_1552);
if (lean_is_scalar(x_1556)) {
 x_1558 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1558 = x_1556;
}
lean_ctor_set(x_1558, 0, x_1557);
return x_1558;
}
else
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
lean_dec_ref(x_1552);
lean_dec(x_1542);
x_1559 = lean_ctor_get(x_1555, 0);
lean_inc(x_1559);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 x_1560 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1560 = lean_box(0);
}
if (lean_is_scalar(x_1560)) {
 x_1561 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1561 = x_1560;
}
lean_ctor_set(x_1561, 0, x_1559);
return x_1561;
}
}
block_1568:
{
if (lean_obj_tag(x_1564) == 0)
{
lean_dec_ref(x_1564);
x_1553 = x_1563;
x_1554 = lean_box(0);
goto block_1562;
}
else
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
lean_dec(x_1563);
lean_dec_ref(x_1552);
lean_dec(x_1542);
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
if (lean_is_exclusive(x_1564)) {
 lean_ctor_release(x_1564, 0);
 x_1566 = x_1564;
} else {
 lean_dec_ref(x_1564);
 x_1566 = lean_box(0);
}
if (lean_is_scalar(x_1566)) {
 x_1567 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1567 = x_1566;
}
lean_ctor_set(x_1567, 0, x_1565);
return x_1567;
}
}
block_1585:
{
uint8_t x_1576; 
x_1576 = lean_nat_dec_lt(x_1544, x_1572);
if (x_1576 == 0)
{
lean_dec(x_1574);
lean_dec(x_1572);
lean_dec_ref(x_1571);
lean_dec_ref(x_1570);
lean_dec(x_1569);
lean_dec(x_1549);
x_1553 = x_1573;
x_1554 = lean_box(0);
goto block_1562;
}
else
{
lean_object* x_1577; uint8_t x_1578; 
x_1577 = lean_box(0);
x_1578 = lean_nat_dec_le(x_1572, x_1572);
if (x_1578 == 0)
{
if (x_1576 == 0)
{
lean_dec(x_1574);
lean_dec(x_1572);
lean_dec_ref(x_1571);
lean_dec_ref(x_1570);
lean_dec(x_1569);
lean_dec(x_1549);
x_1553 = x_1573;
x_1554 = lean_box(0);
goto block_1562;
}
else
{
size_t x_1579; size_t x_1580; lean_object* x_1581; 
x_1579 = 0;
x_1580 = lean_usize_of_nat(x_1572);
lean_dec(x_1572);
x_1581 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1549, x_1579, x_1580, x_1577, x_1571, x_1574, x_1570, x_1569);
lean_dec(x_1569);
lean_dec_ref(x_1570);
lean_dec(x_1574);
lean_dec_ref(x_1571);
lean_dec(x_1549);
x_1563 = x_1573;
x_1564 = x_1581;
goto block_1568;
}
}
else
{
size_t x_1582; size_t x_1583; lean_object* x_1584; 
x_1582 = 0;
x_1583 = lean_usize_of_nat(x_1572);
lean_dec(x_1572);
x_1584 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1549, x_1582, x_1583, x_1577, x_1571, x_1574, x_1570, x_1569);
lean_dec(x_1569);
lean_dec_ref(x_1570);
lean_dec(x_1574);
lean_dec_ref(x_1571);
lean_dec(x_1549);
x_1563 = x_1573;
x_1564 = x_1584;
goto block_1568;
}
}
}
block_1590:
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
if (lean_is_scalar(x_1536)) {
 x_1587 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1587 = x_1536;
}
lean_ctor_set(x_1587, 0, x_1532);
lean_ctor_set(x_1587, 1, x_1552);
lean_ctor_set(x_1587, 2, x_1541);
lean_ctor_set(x_1587, 3, x_1549);
x_1588 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1588, 0, x_1587);
if (lean_is_scalar(x_1550)) {
 x_1589 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1589 = x_1550;
}
lean_ctor_set(x_1589, 0, x_1588);
return x_1589;
}
block_1595:
{
if (x_1592 == 0)
{
lean_dec(x_1547);
lean_dec(x_1534);
lean_dec_ref(x_1);
x_1586 = lean_box(0);
goto block_1590;
}
else
{
uint8_t x_1593; 
x_1593 = l_Lean_instBEqFVarId_beq(x_1534, x_1541);
lean_dec(x_1534);
if (x_1593 == 0)
{
lean_dec(x_1547);
lean_dec_ref(x_1);
x_1586 = lean_box(0);
goto block_1590;
}
else
{
lean_object* x_1594; 
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec(x_1532);
if (lean_is_scalar(x_1547)) {
 x_1594 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1594 = x_1547;
}
lean_ctor_set(x_1594, 0, x_1);
return x_1594;
}
}
}
block_1617:
{
lean_object* x_1602; uint8_t x_1603; 
x_1602 = lean_array_get_size(x_1549);
x_1603 = lean_nat_dec_lt(x_1544, x_1602);
if (x_1603 == 0)
{
lean_dec(x_1550);
lean_dec(x_1547);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_1569 = x_1600;
x_1570 = x_1599;
x_1571 = x_1597;
x_1572 = x_1602;
x_1573 = x_1596;
x_1574 = x_1598;
x_1575 = lean_box(0);
goto block_1585;
}
else
{
if (x_1603 == 0)
{
lean_dec(x_1550);
lean_dec(x_1547);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_1);
x_1569 = x_1600;
x_1570 = x_1599;
x_1571 = x_1597;
x_1572 = x_1602;
x_1573 = x_1596;
x_1574 = x_1598;
x_1575 = lean_box(0);
goto block_1585;
}
else
{
size_t x_1604; size_t x_1605; uint8_t x_1606; 
x_1604 = 0;
x_1605 = lean_usize_of_nat(x_1602);
x_1606 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_109, x_110, x_1549, x_1604, x_1605);
lean_dec(x_110);
lean_dec(x_109);
if (x_1606 == 0)
{
lean_dec(x_1550);
lean_dec(x_1547);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1);
x_1569 = x_1600;
x_1570 = x_1599;
x_1571 = x_1597;
x_1572 = x_1602;
x_1573 = x_1596;
x_1574 = x_1598;
x_1575 = lean_box(0);
goto block_1585;
}
else
{
if (x_122 == 0)
{
lean_object* x_1607; 
lean_dec(x_1600);
lean_dec_ref(x_1599);
lean_dec(x_1598);
lean_dec_ref(x_1597);
lean_dec(x_1542);
lean_inc(x_1541);
x_1607 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1541, x_1596);
lean_dec(x_1596);
if (lean_obj_tag(x_1607) == 0)
{
size_t x_1608; size_t x_1609; uint8_t x_1610; 
lean_dec_ref(x_1607);
x_1608 = lean_ptr_addr(x_1535);
lean_dec_ref(x_1535);
x_1609 = lean_ptr_addr(x_1549);
x_1610 = lean_usize_dec_eq(x_1608, x_1609);
if (x_1610 == 0)
{
lean_dec_ref(x_1533);
x_1591 = lean_box(0);
x_1592 = x_1610;
goto block_1595;
}
else
{
size_t x_1611; size_t x_1612; uint8_t x_1613; 
x_1611 = lean_ptr_addr(x_1533);
lean_dec_ref(x_1533);
x_1612 = lean_ptr_addr(x_1552);
x_1613 = lean_usize_dec_eq(x_1611, x_1612);
x_1591 = lean_box(0);
x_1592 = x_1613;
goto block_1595;
}
}
else
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
lean_dec_ref(x_1552);
lean_dec(x_1550);
lean_dec(x_1549);
lean_dec(x_1547);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1);
x_1614 = lean_ctor_get(x_1607, 0);
lean_inc(x_1614);
if (lean_is_exclusive(x_1607)) {
 lean_ctor_release(x_1607, 0);
 x_1615 = x_1607;
} else {
 lean_dec_ref(x_1607);
 x_1615 = lean_box(0);
}
if (lean_is_scalar(x_1615)) {
 x_1616 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1616 = x_1615;
}
lean_ctor_set(x_1616, 0, x_1614);
return x_1616;
}
}
else
{
lean_dec(x_1550);
lean_dec(x_1547);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec_ref(x_1);
x_1569 = x_1600;
x_1570 = x_1599;
x_1571 = x_1597;
x_1572 = x_1602;
x_1573 = x_1596;
x_1574 = x_1598;
x_1575 = lean_box(0);
goto block_1585;
}
}
}
}
}
}
else
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; 
lean_dec(x_1547);
lean_dec(x_1543);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec(x_1529);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1662 = lean_ctor_get(x_1548, 0);
lean_inc(x_1662);
if (lean_is_exclusive(x_1548)) {
 lean_ctor_release(x_1548, 0);
 x_1663 = x_1548;
} else {
 lean_dec_ref(x_1548);
 x_1663 = lean_box(0);
}
if (lean_is_scalar(x_1663)) {
 x_1664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1664 = x_1663;
}
lean_ctor_set(x_1664, 0, x_1662);
return x_1664;
}
}
else
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; 
lean_dec(x_1543);
lean_dec(x_1542);
lean_dec(x_1541);
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec(x_1529);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1665 = lean_ctor_get(x_1545, 0);
lean_inc(x_1665);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 x_1666 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1666 = lean_box(0);
}
if (lean_is_scalar(x_1666)) {
 x_1667 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1667 = x_1666;
}
lean_ctor_set(x_1667, 0, x_1665);
return x_1667;
}
}
else
{
lean_object* x_1668; 
lean_dec(x_1536);
lean_dec_ref(x_1535);
lean_dec(x_1534);
lean_dec_ref(x_1533);
lean_dec(x_1532);
lean_dec(x_1529);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1668 = l_Lean_Compiler_LCNF_mkReturnErased(x_1539, x_5, x_6, x_1289, x_8);
lean_dec(x_8);
lean_dec_ref(x_1289);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1668;
}
}
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; 
lean_dec_ref(x_1526);
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1669 = lean_ctor_get(x_1527, 0);
lean_inc(x_1669);
if (lean_is_exclusive(x_1527)) {
 lean_ctor_release(x_1527, 0);
 x_1670 = x_1527;
} else {
 lean_dec_ref(x_1527);
 x_1670 = lean_box(0);
}
if (lean_is_scalar(x_1670)) {
 x_1671 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1671 = x_1670;
}
lean_ctor_set(x_1671, 0, x_1669);
return x_1671;
}
}
case 5:
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
lean_dec(x_1237);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1672 = lean_ctor_get(x_1, 0);
x_1673 = lean_st_ref_get(x_3);
x_1674 = lean_ctor_get(x_1673, 0);
lean_inc_ref(x_1674);
lean_dec(x_1673);
lean_inc(x_1672);
x_1675 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_1674, x_1672, x_122);
lean_dec_ref(x_1674);
if (lean_obj_tag(x_1675) == 0)
{
lean_object* x_1676; lean_object* x_1677; 
lean_dec_ref(x_1289);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_1676 = lean_ctor_get(x_1675, 0);
lean_inc(x_1676);
lean_dec_ref(x_1675);
lean_inc(x_1676);
x_1677 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_1676, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_1677) == 0)
{
lean_object* x_1678; uint8_t x_1679; 
if (lean_is_exclusive(x_1677)) {
 lean_ctor_release(x_1677, 0);
 x_1678 = x_1677;
} else {
 lean_dec_ref(x_1677);
 x_1678 = lean_box(0);
}
x_1679 = l_Lean_instBEqFVarId_beq(x_1672, x_1676);
if (x_1679 == 0)
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1680 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1680 = lean_box(0);
}
if (lean_is_scalar(x_1680)) {
 x_1681 = lean_alloc_ctor(5, 1, 0);
} else {
 x_1681 = x_1680;
}
lean_ctor_set(x_1681, 0, x_1676);
if (lean_is_scalar(x_1678)) {
 x_1682 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1682 = x_1678;
}
lean_ctor_set(x_1682, 0, x_1681);
return x_1682;
}
else
{
lean_object* x_1683; 
lean_dec(x_1676);
if (lean_is_scalar(x_1678)) {
 x_1683 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1683 = x_1678;
}
lean_ctor_set(x_1683, 0, x_1);
return x_1683;
}
}
else
{
lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_1676);
lean_dec_ref(x_1);
x_1684 = lean_ctor_get(x_1677, 0);
lean_inc(x_1684);
if (lean_is_exclusive(x_1677)) {
 lean_ctor_release(x_1677, 0);
 x_1685 = x_1677;
} else {
 lean_dec_ref(x_1677);
 x_1685 = lean_box(0);
}
if (lean_is_scalar(x_1685)) {
 x_1686 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1686 = x_1685;
}
lean_ctor_set(x_1686, 0, x_1684);
return x_1686;
}
}
else
{
uint8_t x_1687; lean_object* x_1688; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1687 = 0;
x_1688 = l_Lean_Compiler_LCNF_mkReturnErased(x_1687, x_5, x_6, x_1289, x_8);
lean_dec(x_8);
lean_dec_ref(x_1289);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_1688;
}
}
case 6:
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; uint8_t x_1692; lean_object* x_1693; size_t x_1694; size_t x_1695; uint8_t x_1696; 
lean_dec_ref(x_1289);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_1689 = lean_ctor_get(x_1, 0);
x_1690 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_1691 = lean_ctor_get(x_1690, 0);
lean_inc_ref(x_1691);
lean_dec(x_1690);
x_1692 = 0;
lean_inc_ref(x_1689);
x_1693 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1692, x_1691, x_122, x_1689);
lean_dec_ref(x_1691);
x_1694 = lean_ptr_addr(x_1689);
x_1695 = lean_ptr_addr(x_1693);
x_1696 = lean_usize_dec_eq(x_1694, x_1695);
if (x_1696 == 0)
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_1697 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1697 = lean_box(0);
}
if (lean_is_scalar(x_1697)) {
 x_1698 = lean_alloc_ctor(6, 1, 0);
} else {
 x_1698 = x_1697;
}
lean_ctor_set(x_1698, 0, x_1693);
if (lean_is_scalar(x_1237)) {
 x_1699 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1699 = x_1237;
}
lean_ctor_set(x_1699, 0, x_1698);
return x_1699;
}
else
{
lean_object* x_1700; 
lean_dec_ref(x_1693);
if (lean_is_scalar(x_1237)) {
 x_1700 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1700 = x_1237;
}
lean_ctor_set(x_1700, 0, x_1);
return x_1700;
}
}
default: 
{
lean_object* x_1701; lean_object* x_1702; 
lean_dec(x_1237);
lean_dec(x_110);
lean_dec(x_109);
x_1701 = lean_ctor_get(x_1, 0);
x_1702 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_1702);
lean_inc_ref(x_1701);
x_1238 = x_1701;
x_1239 = x_1702;
x_1240 = x_2;
x_1241 = x_3;
x_1242 = x_4;
x_1243 = x_5;
x_1244 = x_6;
x_1245 = x_1289;
x_1246 = x_8;
goto block_1286;
}
}
block_1286:
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1247 = lean_ctor_get(x_1238, 0);
x_1248 = lean_ctor_get(x_1238, 2);
x_1249 = lean_ctor_get(x_1238, 3);
x_1250 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_1247, x_1241);
if (lean_obj_tag(x_1250) == 0)
{
lean_object* x_1251; uint8_t x_1252; uint8_t x_1253; 
x_1251 = lean_ctor_get(x_1250, 0);
lean_inc(x_1251);
lean_dec_ref(x_1250);
x_1252 = 0;
x_1253 = lean_unbox(x_1251);
if (x_1253 == 0)
{
uint8_t x_1254; 
x_1254 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
if (x_1254 == 0)
{
uint8_t x_1255; 
x_1255 = lean_unbox(x_1251);
lean_dec(x_1251);
x_81 = x_1239;
x_82 = x_1255;
x_83 = x_1238;
x_84 = x_1240;
x_85 = x_1241;
x_86 = x_1242;
x_87 = x_1243;
x_88 = x_1244;
x_89 = x_1245;
x_90 = x_1246;
x_91 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_1256; 
lean_inc_ref(x_1249);
x_1256 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1249, x_1248);
if (x_1256 == 0)
{
uint8_t x_1257; 
x_1257 = lean_unbox(x_1251);
lean_dec(x_1251);
x_81 = x_1239;
x_82 = x_1257;
x_83 = x_1238;
x_84 = x_1240;
x_85 = x_1241;
x_86 = x_1242;
x_87 = x_1243;
x_88 = x_1244;
x_89 = x_1245;
x_90 = x_1246;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1258 = lean_st_ref_get(x_1241);
x_1259 = lean_ctor_get(x_1258, 0);
lean_inc_ref(x_1259);
lean_dec(x_1258);
x_1260 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1252, x_122, x_1238, x_1259, x_1243, x_1244, x_1245, x_1246);
lean_dec_ref(x_1259);
if (lean_obj_tag(x_1260) == 0)
{
lean_object* x_1261; lean_object* x_1262; 
x_1261 = lean_ctor_get(x_1260, 0);
lean_inc(x_1261);
lean_dec_ref(x_1260);
lean_inc(x_1246);
lean_inc_ref(x_1245);
lean_inc(x_1244);
lean_inc_ref(x_1243);
x_1262 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1261, x_1243, x_1244, x_1245, x_1246);
if (lean_obj_tag(x_1262) == 0)
{
lean_object* x_1263; lean_object* x_1264; 
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
lean_dec_ref(x_1262);
x_1264 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_1241);
if (lean_obj_tag(x_1264) == 0)
{
uint8_t x_1265; 
lean_dec_ref(x_1264);
x_1265 = lean_unbox(x_1251);
lean_dec(x_1251);
x_81 = x_1239;
x_82 = x_1265;
x_83 = x_1263;
x_84 = x_1240;
x_85 = x_1241;
x_86 = x_1242;
x_87 = x_1243;
x_88 = x_1244;
x_89 = x_1245;
x_90 = x_1246;
x_91 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
lean_dec(x_1263);
lean_dec(x_1251);
lean_dec(x_1246);
lean_dec_ref(x_1245);
lean_dec(x_1244);
lean_dec_ref(x_1243);
lean_dec_ref(x_1242);
lean_dec(x_1241);
lean_dec_ref(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1);
x_1266 = lean_ctor_get(x_1264, 0);
lean_inc(x_1266);
if (lean_is_exclusive(x_1264)) {
 lean_ctor_release(x_1264, 0);
 x_1267 = x_1264;
} else {
 lean_dec_ref(x_1264);
 x_1267 = lean_box(0);
}
if (lean_is_scalar(x_1267)) {
 x_1268 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1268 = x_1267;
}
lean_ctor_set(x_1268, 0, x_1266);
return x_1268;
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1251);
lean_dec(x_1246);
lean_dec_ref(x_1245);
lean_dec(x_1244);
lean_dec_ref(x_1243);
lean_dec_ref(x_1242);
lean_dec(x_1241);
lean_dec_ref(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1);
x_1269 = lean_ctor_get(x_1262, 0);
lean_inc(x_1269);
if (lean_is_exclusive(x_1262)) {
 lean_ctor_release(x_1262, 0);
 x_1270 = x_1262;
} else {
 lean_dec_ref(x_1262);
 x_1270 = lean_box(0);
}
if (lean_is_scalar(x_1270)) {
 x_1271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1271 = x_1270;
}
lean_ctor_set(x_1271, 0, x_1269);
return x_1271;
}
}
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
lean_dec(x_1251);
lean_dec(x_1246);
lean_dec_ref(x_1245);
lean_dec(x_1244);
lean_dec_ref(x_1243);
lean_dec_ref(x_1242);
lean_dec(x_1241);
lean_dec_ref(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1);
x_1272 = lean_ctor_get(x_1260, 0);
lean_inc(x_1272);
if (lean_is_exclusive(x_1260)) {
 lean_ctor_release(x_1260, 0);
 x_1273 = x_1260;
} else {
 lean_dec_ref(x_1260);
 x_1273 = lean_box(0);
}
if (lean_is_scalar(x_1273)) {
 x_1274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1274 = x_1273;
}
lean_ctor_set(x_1274, 0, x_1272);
return x_1274;
}
}
}
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1275 = lean_st_ref_get(x_1241);
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc_ref(x_1276);
lean_dec(x_1275);
x_1277 = l_Lean_Compiler_LCNF_normFunDeclImp(x_1252, x_122, x_1238, x_1276, x_1243, x_1244, x_1245, x_1246);
lean_dec_ref(x_1276);
if (lean_obj_tag(x_1277) == 0)
{
lean_object* x_1278; uint8_t x_1279; 
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
lean_dec_ref(x_1277);
x_1279 = lean_unbox(x_1251);
lean_dec(x_1251);
x_49 = x_1239;
x_50 = x_1279;
x_51 = x_1278;
x_52 = x_1240;
x_53 = x_1241;
x_54 = x_1242;
x_55 = x_1243;
x_56 = x_1244;
x_57 = x_1245;
x_58 = x_1246;
x_59 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_1251);
lean_dec(x_1246);
lean_dec_ref(x_1245);
lean_dec(x_1244);
lean_dec_ref(x_1243);
lean_dec_ref(x_1242);
lean_dec(x_1241);
lean_dec_ref(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1);
x_1280 = lean_ctor_get(x_1277, 0);
lean_inc(x_1280);
if (lean_is_exclusive(x_1277)) {
 lean_ctor_release(x_1277, 0);
 x_1281 = x_1277;
} else {
 lean_dec_ref(x_1277);
 x_1281 = lean_box(0);
}
if (lean_is_scalar(x_1281)) {
 x_1282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1282 = x_1281;
}
lean_ctor_set(x_1282, 0, x_1280);
return x_1282;
}
}
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
lean_dec(x_1246);
lean_dec_ref(x_1245);
lean_dec(x_1244);
lean_dec_ref(x_1243);
lean_dec_ref(x_1242);
lean_dec(x_1241);
lean_dec_ref(x_1240);
lean_dec_ref(x_1239);
lean_dec_ref(x_1238);
lean_dec_ref(x_1);
x_1283 = lean_ctor_get(x_1250, 0);
lean_inc(x_1283);
if (lean_is_exclusive(x_1250)) {
 lean_ctor_release(x_1250, 0);
 x_1284 = x_1250;
} else {
 lean_dec_ref(x_1250);
 x_1284 = lean_box(0);
}
if (lean_is_scalar(x_1284)) {
 x_1285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1285 = x_1284;
}
lean_ctor_set(x_1285, 0, x_1283);
return x_1285;
}
}
}
else
{
lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1703 = lean_ctor_get(x_1236, 0);
lean_inc(x_1703);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 x_1704 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1704 = lean_box(0);
}
if (lean_is_scalar(x_1704)) {
 x_1705 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1705 = x_1704;
}
lean_ctor_set(x_1705, 0, x_1703);
return x_1705;
}
}
}
else
{
lean_object* x_1706; 
lean_dec_ref(x_1);
x_1706 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1706;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
}
block_25:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
block_48:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ptr_addr(x_30);
x_32 = lean_ptr_addr(x_27);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
x_18 = x_26;
x_19 = x_27;
x_20 = lean_box(0);
x_21 = x_33;
goto block_25;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_29);
x_35 = lean_ptr_addr(x_26);
x_36 = lean_usize_dec_eq(x_34, x_35);
x_18 = x_26;
x_19 = x_27;
x_20 = lean_box(0);
x_21 = x_36;
goto block_25;
}
}
case 2:
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ptr_addr(x_38);
x_40 = lean_ptr_addr(x_27);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
x_10 = x_26;
x_11 = x_27;
x_12 = lean_box(0);
x_13 = x_41;
goto block_17;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_37);
x_43 = lean_ptr_addr(x_26);
x_44 = lean_usize_dec_eq(x_42, x_43);
x_10 = x_26;
x_11 = x_27;
x_12 = lean_box(0);
x_13 = x_44;
goto block_17;
}
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_45 = l_Lean_Compiler_LCNF_Simp_simp___closed__3;
x_46 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
block_80:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
x_60 = l_Lean_Compiler_LCNF_Simp_simp(x_49, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_51, 0);
x_63 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_62, x_53);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec_ref(x_1);
x_66 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_51, x_53, x_56);
lean_dec(x_56);
lean_dec(x_53);
lean_dec_ref(x_51);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_61);
return x_66;
}
else
{
lean_object* x_69; 
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_61);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_61);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
if (x_50 == 0)
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
x_26 = x_51;
x_27 = x_61;
x_28 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_73; 
lean_inc_ref(x_51);
x_73 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_26 = x_51;
x_27 = x_61;
x_28 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_74; 
lean_dec(x_61);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_63, 0);
lean_inc(x_78);
lean_dec(x_63);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
return x_60;
}
}
block_97:
{
lean_object* x_92; 
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_84);
x_92 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_49 = x_81;
x_50 = x_82;
x_51 = x_93;
x_52 = x_84;
x_53 = x_85;
x_54 = x_86;
x_55 = x_87;
x_56 = x_88;
x_57 = x_89;
x_58 = x_90;
x_59 = lean_box(0);
goto block_80;
}
else
{
uint8_t x_94; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_81);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
block_105:
{
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_98);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_1);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_st_ref_get(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = 0;
x_16 = 0;
lean_inc_ref(x_11);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_14, x_16, x_11);
lean_dec_ref(x_14);
lean_inc_ref(x_10);
x_18 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16(x_15, x_16, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_6);
lean_inc_ref(x_12);
x_20 = l_Lean_Compiler_LCNF_Simp_simp(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_15, x_1, x_17, x_19, x_21, x_6);
lean_dec(x_6);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__14(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__16_spec__17(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__8(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0_spec__7_spec__18___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
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
l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0_spec__0___redArg___closed__2);
l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0 = _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__2___closed__0);
l_Lean_Compiler_LCNF_Simp_simp___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simp___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0);
l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3);
l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
