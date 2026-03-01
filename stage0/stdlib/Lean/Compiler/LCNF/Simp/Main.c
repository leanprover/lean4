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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value;
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
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0;
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simp___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simp___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value;
lean_object* l_Subarray_copy___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0(void) {
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
x_11 = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_instHashableFVarId_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_instHashableFVarId_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_43; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
x_10 = x_4;
x_11 = x_43;
goto block_42;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
if (x_11 == 0)
{
x_16 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_9);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_38; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_8, 0);
lean_dec(x_41);
x_20 = x_8;
x_21 = x_38;
goto block_37;
}
else
{
lean_dec(x_8);
x_20 = lean_box(0);
x_21 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_array_fget(x_12, x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_13, x_25);
lean_dec(x_13);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_26);
x_27 = x_20;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_14);
x_27 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_28; lean_object* x_29; 
lean_inc(x_23);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_9, x_23, x_24);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_27);
x_29 = x_10;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
x_29 = x_34;
goto block_33;
}
block_33:
{
size_t x_30; size_t x_31; 
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_4 = x_29;
goto _start;
}
}
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_60; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_60 = !lean_is_exclusive(x_1);
if (x_60 == 0)
{
x_11 = x_1;
x_12 = x_60;
goto block_59;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_9, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_58; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
x_17 = x_2;
x_18 = x_58;
goto block_57;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_array_fget_borrowed(x_8, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
x_22 = 0;
lean_inc_ref(x_21);
x_23 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_22, x_21, x_16, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = 0;
x_26 = l_Lean_Compiler_LCNF_mkAuxParam(x_22, x_24, x_25, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_9, x_29);
lean_dec(x_9);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_30);
x_31 = x_11;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_10);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_array_push(x_15, x_27);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_34 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_16, x_20, x_33);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_34);
lean_ctor_set(x_17, 0, x_32);
x_35 = x_17;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
x_35 = x_38;
goto block_37;
}
block_37:
{
x_1 = x_31;
x_2 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_20);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_41 = lean_ctor_get(x_26, 0);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
x_42 = x_26;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_20);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_49 = lean_ctor_get(x_23, 0);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
x_50 = x_23;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_23);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
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
x_14 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1, &l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_71; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_21, 0);
lean_dec(x_72);
x_23 = x_21;
x_24 = x_71;
goto block_70;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_68; uint8_t x_69; 
x_25 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2));
x_68 = lean_array_get_size(x_10);
x_69 = lean_nat_dec_le(x_15, x_13);
if (x_69 == 0)
{
x_26 = x_15;
x_27 = x_68;
goto block_67;
}
else
{
x_26 = x_13;
x_27 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Array_toSubarray___redArg(x_10, x_26, x_27);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_29 = x_23;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_25);
lean_ctor_set(x_66, 1, x_22);
x_29 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_30; 
x_30 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(x_28, x_29, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_35 = l_Lean_Compiler_LCNF_Code_internalize(x_34, x_11, x_33, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = 0;
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_36, x_37, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_38);
x_39 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
x_40 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_32, x_36, x_39, x_5, x_6, x_7, x_8);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_41 = lean_ctor_get(x_38, 0);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
x_42 = x_38;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_49 = lean_ctor_get(x_35, 0);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
x_50 = x_35;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_35);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_57 = lean_ctor_get(x_30, 0);
x_64 = !lean_is_exclusive(x_30);
if (x_64 == 0)
{
x_58 = x_30;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_30);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_73 = lean_ctor_get(x_20, 0);
x_80 = !lean_is_exclusive(x_20);
if (x_80 == 0)
{
x_74 = x_20;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_20);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_77; 
x_13 = lean_ctor_get(x_12, 0);
x_77 = !lean_is_exclusive(x_12);
if (x_77 == 0)
{
x_14 = x_12;
x_15 = x_77;
goto block_76;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_77;
goto block_76;
}
block_76:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_71; 
lean_del_object(x_14);
x_16 = lean_ctor_get(x_13, 0);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
x_17 = x_13;
x_18 = x_71;
goto block_70;
}
else
{
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_19; 
x_19 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(x_16, x_4, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_61; 
x_20 = lean_ctor_get(x_19, 0);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
x_21 = x_19;
x_22 = x_61;
goto block_60;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_61;
goto block_60;
}
block_60:
{
uint8_t x_23; 
x_23 = lean_unbox(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_24 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_25 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; 
lean_del_object(x_21);
x_28 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec_ref(x_28);
x_29 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_30);
lean_dec(x_16);
x_31 = 0;
x_32 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_43; 
x_33 = lean_ctor_get(x_32, 0);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
x_34 = x_32;
x_35 = x_43;
goto block_42;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_33);
x_36 = x_17;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_33);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_del_object(x_17);
x_44 = lean_ctor_get(x_32, 0);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
x_45 = x_32;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_28, 0);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
x_53 = x_28;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_62 = lean_ctor_get(x_19, 0);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
x_63 = x_19;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_19);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_72 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_72);
x_73 = x_14;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_12, 0);
x_85 = !lean_is_exclusive(x_12);
if (x_85 == 0)
{
x_79 = x_12;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_12);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
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
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_isImplicitReducibleCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_188; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 2);
x_188 = !lean_is_exclusive(x_14);
if (x_188 == 0)
{
x_20 = x_14;
x_21 = x_188;
goto block_187;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_st_ref_get(x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = 0;
lean_inc(x_17);
x_25 = l_Lean_Environment_find_x3f(x_23, x_17, x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_27, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_176; 
x_29 = lean_ctor_get(x_28, 0);
x_176 = !lean_is_exclusive(x_28);
if (x_176 == 0)
{
x_30 = x_28;
x_31 = x_176;
goto block_175;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_176;
goto block_175;
}
block_175:
{
uint8_t x_32; 
x_32 = lean_unbox(x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_33 = lean_box(0);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_33);
x_34 = x_30;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_174; 
lean_del_object(x_30);
lean_inc(x_17);
x_37 = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(x_17, x_8);
x_38 = lean_ctor_get(x_37, 0);
x_174 = !lean_is_exclusive(x_37);
if (x_174 == 0)
{
x_39 = x_37;
x_40 = x_174;
goto block_173;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_172; 
x_41 = lean_ctor_get(x_38, 0);
x_172 = !lean_is_exclusive(x_38);
if (x_172 == 0)
{
x_42 = x_38;
x_43 = x_172;
goto block_171;
}
else
{
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = x_172;
goto block_171;
}
block_171:
{
uint8_t x_44; 
x_44 = lean_unbox(x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
lean_del_object(x_39);
x_45 = l_Lean_Compiler_LCNF_getPhase___redArg(x_5);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_158; 
x_46 = lean_ctor_get(x_45, 0);
x_158 = !lean_is_exclusive(x_45);
if (x_158 == 0)
{
x_47 = x_45;
x_48 = x_158;
goto block_157;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = x_158;
goto block_157;
}
block_157:
{
uint8_t x_49; lean_object* x_50; 
x_49 = lean_unbox(x_46);
lean_inc(x_17);
x_50 = l_Lean_Compiler_LCNF_getDeclAt_x3f(x_17, x_49, x_7, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_148; 
x_51 = lean_ctor_get(x_50, 0);
x_148 = !lean_is_exclusive(x_50);
if (x_148 == 0)
{
x_52 = x_50;
x_53 = x_148;
goto block_147;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_148;
goto block_147;
}
block_147:
{
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_146; 
x_59 = lean_ctor_get(x_51, 0);
x_146 = !lean_is_exclusive(x_51);
if (x_146 == 0)
{
x_60 = x_51;
x_61 = x_146;
goto block_145;
}
else
{
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_box(0);
x_61 = x_146;
goto block_145;
}
block_145:
{
uint8_t x_62; uint8_t x_63; 
x_62 = lean_unbox(x_46);
lean_dec(x_46);
x_63 = l_Lean_Compiler_LCNF_Phase_toPurity(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_del_object(x_52);
x_64 = lean_array_get_size(x_19);
x_65 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_59);
lean_dec(x_59);
x_66 = lean_nat_dec_lt(x_64, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_del_object(x_60);
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_67 = lean_box(0);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_67);
x_68 = x_47;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
else
{
lean_object* x_71; 
lean_del_object(x_47);
lean_inc_ref(x_16);
x_71 = l_Lean_Compiler_LCNF_mkNewParams(x_63, x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_array_size(x_72);
x_74 = 0;
lean_inc(x_72);
x_75 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(x_73, x_74, x_72);
x_76 = l_Array_append___redArg(x_19, x_75);
lean_dec_ref(x_75);
if (x_21 == 0)
{
lean_ctor_set(x_20, 2, x_76);
x_77 = x_20;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_136, 0, x_17);
lean_ctor_set(x_136, 1, x_18);
lean_ctor_set(x_136, 2, x_76);
x_77 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_78; lean_object* x_79; 
x_78 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_79 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_63, x_77, x_78, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (x_43 == 0)
{
lean_ctor_set_tag(x_42, 5);
lean_ctor_set(x_42, 0, x_81);
x_82 = x_42;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_126, 0, x_81);
x_82 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_85 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_72, x_83, x_84, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_inc(x_15);
x_88 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_15, x_87, x_3, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec_ref(x_88);
x_89 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_1, x_3, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_99; 
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_89, 0);
lean_dec(x_100);
x_90 = x_89;
x_91 = x_99;
goto block_98;
}
else
{
lean_dec(x_89);
x_90 = lean_box(0);
x_91 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_92; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_86);
x_92 = x_60;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_86);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_91 == 0)
{
lean_ctor_set(x_90, 0, x_92);
x_93 = x_90;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_86);
lean_del_object(x_60);
x_101 = lean_ctor_get(x_89, 0);
x_108 = !lean_is_exclusive(x_89);
if (x_108 == 0)
{
x_102 = x_89;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_89);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_86);
lean_del_object(x_60);
lean_dec(x_6);
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_88, 0);
x_116 = !lean_is_exclusive(x_88);
if (x_116 == 0)
{
x_110 = x_88;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_88);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_124; 
lean_del_object(x_60);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_117 = lean_ctor_get(x_85, 0);
x_124 = !lean_is_exclusive(x_85);
if (x_124 == 0)
{
x_118 = x_85;
x_119 = x_124;
goto block_123;
}
else
{
lean_inc(x_117);
lean_dec(x_85);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_72);
lean_del_object(x_60);
lean_del_object(x_42);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_127 = lean_ctor_get(x_79, 0);
x_134 = !lean_is_exclusive(x_79);
if (x_134 == 0)
{
x_128 = x_79;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_79);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_del_object(x_60);
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_71, 0);
x_144 = !lean_is_exclusive(x_71);
if (x_144 == 0)
{
x_138 = x_71;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_71);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
else
{
lean_del_object(x_60);
lean_dec(x_59);
lean_del_object(x_47);
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_58;
}
}
}
else
{
lean_dec(x_51);
lean_del_object(x_47);
lean_dec(x_46);
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_54);
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_del_object(x_47);
lean_dec(x_46);
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_50, 0);
x_156 = !lean_is_exclusive(x_50);
if (x_156 == 0)
{
x_150 = x_50;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_50);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_166; 
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_159 = lean_ctor_get(x_45, 0);
x_166 = !lean_is_exclusive(x_45);
if (x_166 == 0)
{
x_160 = x_45;
x_161 = x_166;
goto block_165;
}
else
{
lean_inc(x_159);
lean_dec(x_45);
x_160 = lean_box(0);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; 
if (x_161 == 0)
{
x_162 = x_160;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_159);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_del_object(x_42);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_167 = lean_box(0);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_167);
x_168 = x_39;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_167);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_184; 
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_28, 0);
x_184 = !lean_is_exclusive(x_28);
if (x_184 == 0)
{
x_178 = x_28;
x_179 = x_184;
goto block_183;
}
else
{
lean_inc(x_177);
lean_dec(x_28);
x_178 = lean_box(0);
x_179 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_180; 
if (x_179 == 0)
{
x_180 = x_178;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_177);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_25);
lean_del_object(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_27; 
x_5 = lean_ctor_get(x_1, 0);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
x_6 = x_1;
x_7 = x_27;
goto block_26;
}
else
{
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_9, x_5, x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
lean_del_object(x_6);
x_12 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_13 = x_11;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_instBEqFVarId_beq(x_12, x_2);
lean_dec(x_12);
x_16 = lean_box(x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(x_10);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_22);
x_23 = x_6;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; lean_object* x_13; lean_object* x_15; 
x_7 = lean_nat_dec_eq(x_1, x_2);
x_8 = 1;
x_15 = lean_array_uget_borrowed(x_3, x_4);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_16);
x_13 = x_16;
goto block_14;
}
case 1:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_13 = x_17;
goto block_14;
}
default: 
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_16, 0);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
x_29 = x_16;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox(x_2);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(x_1, x_2, x_12, x_3, x_5, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_7, x_8, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_14 = x_11;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = lean_name_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1);
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
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = lean_name_eq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint64_t x_10; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_22; 
x_22 = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
x_10 = x_22;
goto block_21;
}
else
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_10 = x_23;
goto block_21;
}
block_21:
{
size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
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
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; 
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_9; 
x_9 = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
x_4 = x_9;
goto block_8;
}
else
{
uint64_t x_10; 
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_4 = x_10;
goto block_8;
}
block_8:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_6 = x_1;
x_7 = x_18;
goto block_17;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_inc_ref(x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
x_11 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_5);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_array_push(x_2, x_12);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_14; uint8_t x_15; uint8_t x_46; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_46 = !lean_is_exclusive(x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_4, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_4, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_4, 0);
lean_dec(x_49);
x_14 = x_4;
x_15 = x_46;
goto block_45;
}
else
{
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_44; 
x_16 = lean_st_ref_take(x_5);
x_17 = lean_array_uget_borrowed(x_1, x_3);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 2);
x_22 = lean_ctor_get(x_16, 3);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*7);
x_24 = lean_ctor_get(x_16, 4);
x_25 = lean_ctor_get(x_16, 5);
x_26 = lean_ctor_get(x_16, 6);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
x_27 = x_16;
x_28 = x_44;
goto block_43;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget_borrowed(x_9, x_10);
lean_inc(x_29);
lean_inc(x_18);
x_30 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_19, x_18, x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_20);
lean_ctor_set(x_42, 2, x_21);
lean_ctor_set(x_42, 3, x_22);
lean_ctor_set(x_42, 4, x_24);
lean_ctor_set(x_42, 5, x_25);
lean_ctor_set(x_42, 6, x_26);
lean_ctor_set_uint8(x_42, sizeof(void*)*7, x_23);
x_31 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_st_ref_set(x_5, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_10, x_33);
lean_dec(x_10);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_34);
x_35 = x_14;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_11);
x_35 = x_40;
goto block_39;
}
block_39:
{
size_t x_36; size_t x_37; 
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_4 = x_35;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_array_uget_borrowed(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_9, x_5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
x_11 = x_9;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_13; 
x_13 = lean_unbox(x_10);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_del_object(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
if (x_12 == 0)
{
x_17 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_array_uget_borrowed(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_8, x_9, x_5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uget_borrowed(x_1, x_2);
x_22 = l_Lean_Compiler_LCNF_Alt_getParams(x_21);
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
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_22, x_27, x_28, x_24, x_6);
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
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_22, x_30, x_31, x_24, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
x_9 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
x_11 = x_9;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_13; 
x_13 = lean_unbox(x_10);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_del_object(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
if (x_12 == 0)
{
x_17 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(x_1, x_6, x_7, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(635u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__1));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simp___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_46; 
x_46 = lean_nat_dec_lt(x_1, x_2);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_47 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_8, x_10, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec_ref(x_47);
x_48 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_49 = lean_ctor_get(x_47, 0);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
x_50 = x_47;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_1, x_7);
if (x_57 == 0)
{
lean_dec(x_7);
x_17 = x_1;
x_18 = x_2;
goto block_45;
}
else
{
lean_dec(x_1);
x_17 = x_7;
x_18 = x_2;
goto block_45;
}
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Array_toSubarray___redArg(x_5, x_17, x_18);
x_20 = l_Subarray_copy___redArg(x_19);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_30 = x_26;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_23, 0);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
x_38 = x_23;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_344; 
x_14 = lean_ctor_get(x_13, 0);
x_344 = !lean_is_exclusive(x_13);
if (x_344 == 0)
{
x_15 = x_13;
x_16 = x_344;
goto block_343;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_344;
goto block_343;
}
block_343:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_338; 
lean_del_object(x_15);
x_17 = lean_ctor_get(x_14, 0);
x_338 = !lean_is_exclusive(x_14);
if (x_338 == 0)
{
x_18 = x_14;
x_19 = x_338;
goto block_337;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 2);
x_23 = lean_ctor_get(x_17, 3);
x_24 = lean_ctor_get_uint8(x_17, sizeof(void*)*4 + 2);
x_25 = lean_array_get_size(x_23);
x_26 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_17);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_12, 0);
lean_inc(x_313);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_313);
x_314 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_24, x_313, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_328; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec_ref(x_314);
x_316 = lean_ctor_get(x_3, 0);
x_317 = lean_ctor_get(x_3, 1);
x_318 = lean_ctor_get(x_3, 2);
x_319 = lean_ctor_get(x_3, 3);
x_328 = !lean_is_exclusive(x_3);
if (x_328 == 0)
{
x_320 = x_3;
x_321 = x_328;
goto block_327;
}
else
{
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_3);
x_320 = lean_box(0);
x_321 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_inc(x_313);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_313);
lean_ctor_set(x_322, 1, x_318);
x_323 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(x_319, x_313, x_315);
if (x_321 == 0)
{
lean_ctor_set(x_320, 3, x_323);
lean_ctor_set(x_320, 2, x_322);
x_324 = x_320;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_326, 0, x_316);
lean_ctor_set(x_326, 1, x_317);
lean_ctor_set(x_326, 2, x_322);
lean_ctor_set(x_326, 3, x_323);
x_324 = x_326;
goto block_325;
}
block_325:
{
x_210 = x_324;
x_211 = x_4;
x_212 = x_5;
x_213 = x_6;
x_214 = x_7;
x_215 = x_8;
x_216 = x_9;
x_217 = lean_box(0);
goto block_312;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_336; 
lean_dec(x_313);
lean_dec(x_26);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_329 = lean_ctor_get(x_314, 0);
x_336 = !lean_is_exclusive(x_314);
if (x_336 == 0)
{
x_330 = x_314;
x_331 = x_336;
goto block_335;
}
else
{
lean_inc(x_329);
lean_dec(x_314);
x_330 = lean_box(0);
x_331 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_332; 
if (x_331 == 0)
{
x_332 = x_330;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_329);
x_332 = x_334;
goto block_333;
}
block_333:
{
return x_332;
}
}
}
}
else
{
lean_dec(x_12);
x_210 = x_3;
x_211 = x_4;
x_212 = x_5;
x_213 = x_6;
x_214 = x_7;
x_215 = x_8;
x_216 = x_9;
x_217 = lean_box(0);
goto block_312;
}
block_209:
{
lean_object* x_42; 
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
lean_inc_ref(x_32);
lean_inc(x_34);
lean_inc_ref(x_30);
x_42 = l_Lean_Compiler_LCNF_Simp_simp(x_40, x_30, x_34, x_32, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_34);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec_ref(x_44);
lean_inc(x_43);
x_45 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_31);
x_46 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
lean_inc_ref(x_46);
x_47 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_28, x_46);
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
x_48 = l_Lean_Compiler_LCNF_inferAppType(x_36, x_22, x_47, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_49);
x_50 = l_Lean_Expr_headBeta(x_49);
x_51 = l_Lean_Expr_isForall(x_50);
lean_dec_ref(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_46);
x_52 = l_Lean_Compiler_LCNF_mkAuxParam(x_36, x_49, x_27, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
lean_inc(x_54);
x_55 = lean_apply_9(x_37, x_54, x_30, x_34, x_32, x_41, x_33, x_38, x_29, lean_box(0));
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_mk_empty_array_with_capacity(x_57);
x_59 = lean_array_push(x_58, x_53);
x_60 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
x_61 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_36, x_59, x_56, x_60, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_62);
x_63 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_57);
x_64 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_36, x_43, x_63, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_76; 
x_65 = lean_ctor_get(x_64, 0);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
x_66 = x_64;
x_67 = x_76;
goto block_75;
}
else
{
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_65);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_68);
x_69 = x_18;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_68);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_69);
x_70 = x_66;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_62);
lean_del_object(x_18);
x_77 = lean_ctor_get(x_64, 0);
x_84 = !lean_is_exclusive(x_64);
if (x_84 == 0)
{
x_78 = x_64;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec(x_33);
lean_dec(x_29);
lean_del_object(x_18);
x_85 = lean_ctor_get(x_61, 0);
x_92 = !lean_is_exclusive(x_61);
if (x_92 == 0)
{
x_86 = x_61;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_61);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_dec(x_53);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec(x_33);
lean_dec(x_29);
lean_del_object(x_18);
x_93 = lean_ctor_get(x_55, 0);
x_100 = !lean_is_exclusive(x_55);
if (x_100 == 0)
{
x_94 = x_55;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_55);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_del_object(x_18);
x_101 = lean_ctor_get(x_52, 0);
x_108 = !lean_is_exclusive(x_52);
if (x_108 == 0)
{
x_102 = x_52;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_52);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_49);
x_109 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
x_110 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_46, x_43, x_109, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
x_112 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_111, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_29);
lean_inc_ref(x_38);
lean_inc(x_33);
lean_inc_ref(x_41);
lean_inc_ref(x_32);
lean_inc(x_34);
lean_inc_ref(x_30);
lean_inc(x_114);
x_115 = lean_apply_9(x_37, x_114, x_30, x_34, x_32, x_41, x_33, x_38, x_29, lean_box(0));
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_113);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_mk_empty_array_with_capacity(x_118);
x_120 = lean_array_push(x_119, x_117);
x_121 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_120, x_116, x_30, x_34, x_32, x_41, x_33, x_38, x_29);
lean_dec(x_29);
lean_dec_ref(x_38);
lean_dec(x_33);
lean_dec_ref(x_41);
lean_dec_ref(x_32);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_132; 
x_122 = lean_ctor_get(x_121, 0);
x_132 = !lean_is_exclusive(x_121);
if (x_132 == 0)
{
x_123 = x_121;
x_124 = x_132;
goto block_131;
}
else
{
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_box(0);
x_124 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_125; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_122);
x_125 = x_18;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_122);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_125);
x_126 = x_123;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
lean_del_object(x_18);
x_133 = lean_ctor_get(x_121, 0);
x_140 = !lean_is_exclusive(x_121);
if (x_140 == 0)
{
x_134 = x_121;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_dec(x_121);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_148; 
lean_dec(x_113);
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_del_object(x_18);
x_141 = lean_ctor_get(x_115, 0);
x_148 = !lean_is_exclusive(x_115);
if (x_148 == 0)
{
x_142 = x_115;
x_143 = x_148;
goto block_147;
}
else
{
lean_inc(x_141);
lean_dec(x_115);
x_142 = lean_box(0);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_143 == 0)
{
x_144 = x_142;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_141);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_del_object(x_18);
x_149 = lean_ctor_get(x_112, 0);
x_156 = !lean_is_exclusive(x_112);
if (x_156 == 0)
{
x_150 = x_112;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_112);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_del_object(x_18);
x_157 = lean_ctor_get(x_110, 0);
x_164 = !lean_is_exclusive(x_110);
if (x_164 == 0)
{
x_158 = x_110;
x_159 = x_164;
goto block_163;
}
else
{
lean_inc(x_157);
lean_dec(x_110);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_157);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_del_object(x_18);
x_165 = lean_ctor_get(x_48, 0);
x_172 = !lean_is_exclusive(x_48);
if (x_172 == 0)
{
x_166 = x_48;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_48);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_object* x_173; 
lean_dec(x_39);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
lean_dec_ref(x_28);
lean_dec_ref(x_22);
x_173 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_36, x_43, x_31, x_41, x_33, x_38, x_29);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_184; 
x_174 = lean_ctor_get(x_173, 0);
x_184 = !lean_is_exclusive(x_173);
if (x_184 == 0)
{
x_175 = x_173;
x_176 = x_184;
goto block_183;
}
else
{
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_177; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_174);
x_177 = x_18;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_174);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_176 == 0)
{
lean_ctor_set(x_175, 0, x_177);
x_178 = x_175;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_177);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_del_object(x_18);
x_185 = lean_ctor_get(x_173, 0);
x_192 = !lean_is_exclusive(x_173);
if (x_192 == 0)
{
x_186 = x_173;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_173);
x_186 = lean_box(0);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_187 == 0)
{
x_188 = x_186;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_185);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_200; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_193 = lean_ctor_get(x_44, 0);
x_200 = !lean_is_exclusive(x_44);
if (x_200 == 0)
{
x_194 = x_44;
x_195 = x_200;
goto block_199;
}
else
{
lean_inc(x_193);
lean_dec(x_44);
x_194 = lean_box(0);
x_195 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_196; 
if (x_195 == 0)
{
x_196 = x_194;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_193);
x_196 = x_198;
goto block_197;
}
block_197:
{
return x_196;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_208; 
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_201 = lean_ctor_get(x_42, 0);
x_208 = !lean_is_exclusive(x_42);
if (x_208 == 0)
{
x_202 = x_42;
x_203 = x_208;
goto block_207;
}
else
{
lean_inc(x_201);
lean_dec(x_42);
x_202 = lean_box(0);
x_203 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_204; 
if (x_203 == 0)
{
x_204 = x_202;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_201);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
}
}
block_312:
{
if (x_27 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_dec(x_17);
x_218 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
lean_inc_ref(x_23);
x_219 = l_Array_toSubarray___redArg(x_23, x_218, x_26);
lean_inc_ref(x_219);
x_220 = l_Subarray_copy___redArg(x_219);
lean_inc(x_216);
lean_inc_ref(x_215);
lean_inc(x_214);
lean_inc_ref(x_213);
x_221 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_20, x_21, x_220, x_27, x_210, x_211, x_212, x_213, x_214, x_215, x_216);
lean_dec_ref(x_20);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = 0;
x_224 = lean_box(x_223);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_26);
x_225 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(x_225, 0, x_26);
lean_closure_set(x_225, 1, x_25);
lean_closure_set(x_225, 2, x_11);
lean_closure_set(x_225, 3, x_2);
lean_closure_set(x_225, 4, x_23);
lean_closure_set(x_225, 5, x_224);
lean_closure_set(x_225, 6, x_218);
lean_inc_ref(x_212);
lean_inc_ref(x_210);
lean_inc_ref(x_225);
lean_inc(x_211);
x_226 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_226, 0, x_211);
lean_closure_set(x_226, 1, x_225);
lean_closure_set(x_226, 2, x_210);
lean_closure_set(x_226, 3, x_212);
x_227 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_2, x_11);
lean_dec(x_11);
lean_dec_ref(x_2);
if (x_227 == 0)
{
lean_dec(x_26);
x_28 = x_219;
x_29 = x_216;
x_30 = x_210;
x_31 = x_226;
x_32 = x_212;
x_33 = x_214;
x_34 = x_211;
x_35 = lean_box(0);
x_36 = x_223;
x_37 = x_225;
x_38 = x_215;
x_39 = x_218;
x_40 = x_222;
x_41 = x_213;
goto block_209;
}
else
{
uint8_t x_228; 
x_228 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
if (x_228 == 0)
{
x_28 = x_219;
x_29 = x_216;
x_30 = x_210;
x_31 = x_226;
x_32 = x_212;
x_33 = x_214;
x_34 = x_211;
x_35 = lean_box(0);
x_36 = x_223;
x_37 = x_225;
x_38 = x_215;
x_39 = x_218;
x_40 = x_222;
x_41 = x_213;
goto block_209;
}
else
{
lean_object* x_229; 
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_219);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_229 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_211);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec_ref(x_229);
x_230 = l_Lean_Compiler_LCNF_Simp_simp(x_222, x_210, x_211, x_212, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_239; 
x_231 = lean_ctor_get(x_230, 0);
x_239 = !lean_is_exclusive(x_230);
if (x_239 == 0)
{
x_232 = x_230;
x_233 = x_239;
goto block_238;
}
else
{
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_box(0);
x_233 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_231);
if (x_233 == 0)
{
lean_ctor_set(x_232, 0, x_234);
x_235 = x_232;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_234);
x_235 = x_237;
goto block_236;
}
block_236:
{
return x_235;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_247; 
x_240 = lean_ctor_get(x_230, 0);
x_247 = !lean_is_exclusive(x_230);
if (x_247 == 0)
{
x_241 = x_230;
x_242 = x_247;
goto block_246;
}
else
{
lean_inc(x_240);
lean_dec(x_230);
x_241 = lean_box(0);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_242 == 0)
{
x_243 = x_241;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_255; 
lean_dec(x_222);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
x_248 = lean_ctor_get(x_229, 0);
x_255 = !lean_is_exclusive(x_229);
if (x_255 == 0)
{
x_249 = x_229;
x_250 = x_255;
goto block_254;
}
else
{
lean_inc(x_248);
lean_dec(x_229);
x_249 = lean_box(0);
x_250 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_251; 
if (x_250 == 0)
{
x_251 = x_249;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_248);
x_251 = x_253;
goto block_252;
}
block_252:
{
return x_251;
}
}
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_263; 
lean_dec_ref(x_219);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_del_object(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_256 = lean_ctor_get(x_221, 0);
x_263 = !lean_is_exclusive(x_221);
if (x_263 == 0)
{
x_257 = x_221;
x_258 = x_263;
goto block_262;
}
else
{
lean_inc(x_256);
lean_dec(x_221);
x_257 = lean_box(0);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_258 == 0)
{
x_259 = x_257;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_256);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
else
{
lean_object* x_264; 
lean_dec(x_26);
lean_del_object(x_18);
lean_inc(x_216);
lean_inc_ref(x_215);
lean_inc(x_214);
lean_inc_ref(x_213);
x_264 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_17, x_210, x_211, x_212, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec_ref(x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_266, x_211, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
lean_dec_ref(x_267);
x_268 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_211);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_dec_ref(x_268);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_2);
x_270 = l_Lean_Compiler_LCNF_Simp_simp(x_269, x_210, x_211, x_212, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_279; 
x_271 = lean_ctor_get(x_270, 0);
x_279 = !lean_is_exclusive(x_270);
if (x_279 == 0)
{
x_272 = x_270;
x_273 = x_279;
goto block_278;
}
else
{
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_box(0);
x_273 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_271);
if (x_273 == 0)
{
lean_ctor_set(x_272, 0, x_274);
x_275 = x_272;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_277, 0, x_274);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_287; 
x_280 = lean_ctor_get(x_270, 0);
x_287 = !lean_is_exclusive(x_270);
if (x_287 == 0)
{
x_281 = x_270;
x_282 = x_287;
goto block_286;
}
else
{
lean_inc(x_280);
lean_dec(x_270);
x_281 = lean_box(0);
x_282 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_283; 
if (x_282 == 0)
{
x_283 = x_281;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_280);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_295; 
lean_dec(x_265);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_2);
x_288 = lean_ctor_get(x_268, 0);
x_295 = !lean_is_exclusive(x_268);
if (x_295 == 0)
{
x_289 = x_268;
x_290 = x_295;
goto block_294;
}
else
{
lean_inc(x_288);
lean_dec(x_268);
x_289 = lean_box(0);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_290 == 0)
{
x_291 = x_289;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_303; 
lean_dec(x_265);
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_2);
x_296 = lean_ctor_get(x_267, 0);
x_303 = !lean_is_exclusive(x_267);
if (x_303 == 0)
{
x_297 = x_267;
x_298 = x_303;
goto block_302;
}
else
{
lean_inc(x_296);
lean_dec(x_267);
x_297 = lean_box(0);
x_298 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_299; 
if (x_298 == 0)
{
x_299 = x_297;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_296);
x_299 = x_301;
goto block_300;
}
block_300:
{
return x_299;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_311; 
lean_dec(x_216);
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_11);
lean_dec_ref(x_2);
x_304 = lean_ctor_get(x_264, 0);
x_311 = !lean_is_exclusive(x_264);
if (x_311 == 0)
{
x_305 = x_264;
x_306 = x_311;
goto block_310;
}
else
{
lean_inc(x_304);
lean_dec(x_264);
x_305 = lean_box(0);
x_306 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_307; 
if (x_306 == 0)
{
x_307 = x_305;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_304);
x_307 = x_309;
goto block_308;
}
block_308:
{
return x_307;
}
}
}
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_14);
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
x_339 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_339);
x_340 = x_15;
goto block_341;
}
else
{
lean_object* x_342; 
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_339);
x_340 = x_342;
goto block_341;
}
block_341:
{
return x_340;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_352; 
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
x_345 = lean_ctor_get(x_13, 0);
x_352 = !lean_is_exclusive(x_13);
if (x_352 == 0)
{
x_346 = x_13;
x_347 = x_352;
goto block_351;
}
else
{
lean_inc(x_345);
lean_dec(x_13);
x_346 = lean_box(0);
x_347 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_348; 
if (x_347 == 0)
{
x_348 = x_346;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_345);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0(void) {
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
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_st_ref_get(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = 0;
lean_inc(x_15);
x_20 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_17, x_15, x_19);
lean_dec_ref(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_21, x_4, x_6, x_8);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_252; 
x_23 = lean_ctor_get(x_22, 0);
x_252 = !lean_is_exclusive(x_22);
if (x_252 == 0)
{
x_24 = x_22;
x_25 = x_252;
goto block_251;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_252;
goto block_251;
}
block_251:
{
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_246; 
x_26 = lean_ctor_get(x_23, 0);
x_246 = !lean_is_exclusive(x_23);
if (x_246 == 0)
{
x_27 = x_23;
x_28 = x_246;
goto block_245;
}
else
{
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_st_ref_get(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_26);
lean_inc(x_31);
x_32 = l_Lean_Environment_find_x3f(x_30, x_31, x_19);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_244; 
x_33 = lean_ctor_get(x_32, 0);
x_244 = !lean_is_exclusive(x_32);
if (x_244 == 0)
{
x_34 = x_32;
x_35 = x_244;
goto block_243;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_244;
goto block_243;
}
block_243:
{
if (lean_obj_tag(x_33) == 6)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_242; 
x_36 = lean_ctor_get(x_33, 0);
x_242 = !lean_is_exclusive(x_33);
if (x_242 == 0)
{
x_37 = x_33;
x_38 = x_242;
goto block_241;
}
else
{
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec_ref(x_36);
x_40 = lean_name_eq(x_14, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_del_object(x_37);
lean_del_object(x_34);
lean_dec(x_31);
lean_del_object(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_box(0);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_41);
x_42 = x_24;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_240; 
lean_del_object(x_24);
x_45 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
x_46 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_18, x_1, x_31);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_ctor_get(x_46, 1);
x_240 = !lean_is_exclusive(x_46);
if (x_240 == 0)
{
x_49 = x_46;
x_50 = x_240;
goto block_239;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_51; 
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 4);
lean_ctor_set(x_37, 0, x_48);
x_51 = x_37;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_238, 0, x_48);
x_51 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_52; 
x_52 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_18, x_51, x_6);
lean_dec_ref(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec_ref(x_52);
x_53 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
if (lean_obj_tag(x_47) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_del_object(x_49);
lean_del_object(x_27);
x_54 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_55);
lean_dec_ref(x_47);
x_56 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_57);
lean_dec_ref(x_26);
x_103 = lean_ctor_get(x_56, 3);
lean_inc(x_103);
lean_dec_ref(x_56);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_array_get_size(x_57);
x_106 = lean_nat_dec_le(x_103, x_104);
if (x_106 == 0)
{
x_58 = x_103;
x_59 = x_105;
goto block_102;
}
else
{
lean_dec(x_103);
x_58 = x_104;
x_59 = x_105;
goto block_102;
}
block_102:
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_60 = l_Array_toSubarray___redArg(x_57, x_58, x_59);
x_61 = lean_array_size(x_54);
x_62 = 0;
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(x_54, x_61, x_62, x_60, x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
lean_inc(x_6);
x_64 = l_Lean_Compiler_LCNF_Simp_simp(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_18, x_54, x_6);
lean_dec(x_6);
lean_dec_ref(x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; uint8_t x_76; 
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_66, 0);
lean_dec(x_77);
x_67 = x_66;
x_68 = x_76;
goto block_75;
}
else
{
lean_dec(x_66);
x_67 = lean_box(0);
x_68 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_69; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_65);
x_69 = x_34;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_65);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_69);
x_70 = x_67;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_65);
lean_del_object(x_34);
x_78 = lean_ctor_get(x_66, 0);
x_85 = !lean_is_exclusive(x_66);
if (x_85 == 0)
{
x_79 = x_66;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec_ref(x_54);
lean_del_object(x_34);
lean_dec(x_6);
x_86 = lean_ctor_get(x_64, 0);
x_93 = !lean_is_exclusive(x_64);
if (x_93 == 0)
{
x_87 = x_64;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_64);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_del_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_94 = lean_ctor_get(x_63, 0);
x_101 = !lean_is_exclusive(x_63);
if (x_101 == 0)
{
x_95 = x_63;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_63);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_199; 
x_107 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_108);
lean_dec_ref(x_47);
x_109 = lean_ctor_get(x_26, 0);
x_199 = !lean_is_exclusive(x_26);
if (x_199 == 0)
{
x_110 = x_26;
x_111 = x_199;
goto block_198;
}
else
{
lean_inc(x_109);
lean_dec(x_26);
x_110 = lean_box(0);
x_111 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_nat_dec_eq(x_109, x_112);
if (x_113 == 1)
{
lean_object* x_114; 
lean_del_object(x_110);
lean_dec(x_109);
lean_dec_ref(x_107);
lean_del_object(x_49);
lean_del_object(x_27);
x_114 = l_Lean_Compiler_LCNF_Simp_simp(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_125; 
x_115 = lean_ctor_get(x_114, 0);
x_125 = !lean_is_exclusive(x_114);
if (x_125 == 0)
{
x_116 = x_114;
x_117 = x_125;
goto block_124;
}
else
{
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(0);
x_117 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_118; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_115);
x_118 = x_34;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_115);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_117 == 0)
{
lean_ctor_set(x_116, 0, x_118);
x_119 = x_116;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_del_object(x_34);
x_126 = lean_ctor_get(x_114, 0);
x_133 = !lean_is_exclusive(x_114);
if (x_133 == 0)
{
x_127 = x_114;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_114);
x_127 = lean_box(0);
x_128 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_129; 
if (x_128 == 0)
{
x_129 = x_127;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_sub(x_109, x_134);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_135);
x_136 = x_110;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_135);
x_136 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_137; 
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_136);
x_137 = x_27;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_136);
x_137 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_138; lean_object* x_139; 
x_138 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_139 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_18, x_137, x_138, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_array_get_borrowed(x_45, x_107, x_112);
x_142 = lean_ctor_get(x_141, 0);
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_inc(x_142);
x_144 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_142, x_143, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec_ref(x_144);
lean_inc(x_6);
x_145 = l_Lean_Compiler_LCNF_Simp_simp(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_18, x_107, x_6);
lean_dec(x_6);
lean_dec_ref(x_107);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; uint8_t x_160; 
x_160 = !lean_is_exclusive(x_147);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_147, 0);
lean_dec(x_161);
x_148 = x_147;
x_149 = x_160;
goto block_159;
}
else
{
lean_dec(x_147);
x_148 = lean_box(0);
x_149 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_150; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_146);
lean_ctor_set(x_49, 0, x_140);
x_150 = x_49;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_140);
lean_ctor_set(x_158, 1, x_146);
x_150 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_151; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_150);
x_151 = x_34;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_150);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_149 == 0)
{
lean_ctor_set(x_148, 0, x_151);
x_152 = x_148;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_151);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_169; 
lean_dec(x_146);
lean_dec(x_140);
lean_del_object(x_49);
lean_del_object(x_34);
x_162 = lean_ctor_get(x_147, 0);
x_169 = !lean_is_exclusive(x_147);
if (x_169 == 0)
{
x_163 = x_147;
x_164 = x_169;
goto block_168;
}
else
{
lean_inc(x_162);
lean_dec(x_147);
x_163 = lean_box(0);
x_164 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_165; 
if (x_164 == 0)
{
x_165 = x_163;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_162);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_dec(x_140);
lean_dec_ref(x_107);
lean_del_object(x_49);
lean_del_object(x_34);
lean_dec(x_6);
x_170 = lean_ctor_get(x_145, 0);
x_177 = !lean_is_exclusive(x_145);
if (x_177 == 0)
{
x_171 = x_145;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_145);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec(x_140);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_del_object(x_49);
lean_del_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_178 = lean_ctor_get(x_144, 0);
x_185 = !lean_is_exclusive(x_144);
if (x_185 == 0)
{
x_179 = x_144;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_144);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_193; 
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_del_object(x_49);
lean_del_object(x_34);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_186 = lean_ctor_get(x_139, 0);
x_193 = !lean_is_exclusive(x_139);
if (x_193 == 0)
{
x_187 = x_139;
x_188 = x_193;
goto block_192;
}
else
{
lean_inc(x_186);
lean_dec(x_139);
x_187 = lean_box(0);
x_188 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_189; 
if (x_188 == 0)
{
x_189 = x_187;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_186);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
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
lean_object* x_200; lean_object* x_201; 
lean_del_object(x_49);
lean_del_object(x_27);
lean_dec(x_26);
x_200 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_200);
lean_dec_ref(x_47);
x_201 = l_Lean_Compiler_LCNF_Simp_simp(x_200, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_212; 
x_202 = lean_ctor_get(x_201, 0);
x_212 = !lean_is_exclusive(x_201);
if (x_212 == 0)
{
x_203 = x_201;
x_204 = x_212;
goto block_211;
}
else
{
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_box(0);
x_204 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_205; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_202);
x_205 = x_34;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_202);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 0, x_205);
x_206 = x_203;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_205);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_del_object(x_34);
x_213 = lean_ctor_get(x_201, 0);
x_220 = !lean_is_exclusive(x_201);
if (x_220 == 0)
{
x_214 = x_201;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_201);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_228; 
lean_del_object(x_49);
lean_dec(x_47);
lean_del_object(x_34);
lean_del_object(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_221 = lean_ctor_get(x_53, 0);
x_228 = !lean_is_exclusive(x_53);
if (x_228 == 0)
{
x_222 = x_53;
x_223 = x_228;
goto block_227;
}
else
{
lean_inc(x_221);
lean_dec(x_53);
x_222 = lean_box(0);
x_223 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_224; 
if (x_223 == 0)
{
x_224 = x_222;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_221);
x_224 = x_226;
goto block_225;
}
block_225:
{
return x_224;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_236; 
lean_del_object(x_49);
lean_dec(x_47);
lean_del_object(x_34);
lean_del_object(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_229 = lean_ctor_get(x_52, 0);
x_236 = !lean_is_exclusive(x_52);
if (x_236 == 0)
{
x_230 = x_52;
x_231 = x_236;
goto block_235;
}
else
{
lean_inc(x_229);
lean_dec(x_52);
x_230 = lean_box(0);
x_231 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_232; 
if (x_231 == 0)
{
x_232 = x_230;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_229);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
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
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_del_object(x_27);
lean_dec(x_26);
lean_del_object(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_del_object(x_27);
lean_dec(x_26);
lean_del_object(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_247 = lean_box(0);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_247);
x_248 = x_24;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_247);
x_248 = x_250;
goto block_249;
}
block_249:
{
return x_248;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_260; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_22, 0);
x_260 = !lean_is_exclusive(x_22);
if (x_260 == 0)
{
x_254 = x_22;
x_255 = x_260;
goto block_259;
}
else
{
lean_inc(x_253);
lean_dec(x_22);
x_254 = lean_box(0);
x_255 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_256; 
if (x_255 == 0)
{
x_256 = x_254;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_253);
x_256 = x_258;
goto block_257;
}
block_257:
{
return x_256;
}
}
}
}
else
{
lean_object* x_261; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_261 = l_Lean_Compiler_LCNF_mkReturnErased(x_18, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_270; 
x_262 = lean_ctor_get(x_261, 0);
x_270 = !lean_is_exclusive(x_261);
if (x_270 == 0)
{
x_263 = x_261;
x_264 = x_270;
goto block_269;
}
else
{
lean_inc(x_262);
lean_dec(x_261);
x_263 = lean_box(0);
x_264 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_262);
if (x_264 == 0)
{
lean_ctor_set(x_263, 0, x_265);
x_266 = x_263;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_268, 0, x_265);
x_266 = x_268;
goto block_267;
}
block_267:
{
return x_266;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
x_271 = lean_ctor_get(x_261, 0);
x_278 = !lean_is_exclusive(x_261);
if (x_278 == 0)
{
x_272 = x_261;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_261);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_89; lean_object* x_90; uint8_t x_91; uint8_t x_93; lean_object* x_94; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
x_33 = lean_ctor_get(x_17, 2);
x_34 = 0;
x_89 = lean_nat_dec_eq(x_2, x_3);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_array_get_size(x_32);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
x_93 = x_89;
x_94 = lean_box(0);
goto block_95;
}
else
{
if (x_98 == 0)
{
x_93 = x_89;
x_94 = lean_box(0);
goto block_95;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_97);
x_101 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_32, x_99, x_100, x_12);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
x_93 = x_103;
x_94 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
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
x_104 = lean_ctor_get(x_101, 0);
x_111 = !lean_is_exclusive(x_101);
if (x_111 == 0)
{
x_105 = x_101;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
block_88:
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
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
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
x_42 = lean_ctor_get(x_39, 0);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
x_43 = x_39;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
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
x_50 = lean_ctor_get(x_37, 0);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
x_51 = x_37;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_33);
x_58 = l_Lean_Compiler_LCNF_Code_inferType(x_34, x_33, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_34, x_33, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec_ref(x_60);
x_61 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_61);
x_62 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_62, 0, x_59);
lean_inc_ref(x_17);
x_63 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_62);
x_18 = x_63;
x_19 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_59);
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
x_64 = lean_ctor_get(x_61, 0);
x_71 = !lean_is_exclusive(x_61);
if (x_71 == 0)
{
x_65 = x_61;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_59);
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
x_72 = lean_ctor_get(x_60, 0);
x_79 = !lean_is_exclusive(x_60);
if (x_79 == 0)
{
x_73 = x_60;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
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
x_80 = lean_ctor_get(x_58, 0);
x_87 = !lean_is_exclusive(x_58);
if (x_87 == 0)
{
x_81 = x_58;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_58);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
block_92:
{
if (x_89 == 0)
{
x_35 = lean_box(0);
x_36 = x_89;
goto block_88;
}
else
{
x_35 = lean_box(0);
x_36 = x_91;
goto block_88;
}
}
block_95:
{
if (lean_obj_tag(x_33) == 6)
{
x_90 = lean_box(0);
x_91 = x_93;
goto block_92;
}
else
{
if (x_89 == 0)
{
x_35 = lean_box(0);
x_36 = x_93;
goto block_88;
}
else
{
x_90 = lean_box(0);
x_91 = x_93;
goto block_92;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_17, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_112);
x_113 = l_Lean_Compiler_LCNF_Simp_simp(x_112, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
lean_inc_ref(x_17);
x_115 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_114);
x_18 = x_115;
x_19 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
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
x_116 = lean_ctor_get(x_113, 0);
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
x_117 = x_113;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; 
x_131 = lean_ctor_get(x_7, 0);
x_132 = lean_ctor_get(x_7, 1);
x_133 = lean_ctor_get(x_7, 2);
x_134 = lean_ctor_get(x_7, 3);
x_135 = lean_ctor_get(x_7, 4);
x_136 = lean_ctor_get(x_7, 5);
x_137 = lean_ctor_get(x_7, 6);
x_138 = lean_ctor_get(x_7, 7);
x_139 = lean_ctor_get(x_7, 8);
x_140 = lean_ctor_get(x_7, 9);
x_141 = lean_ctor_get(x_7, 10);
x_142 = lean_ctor_get(x_7, 11);
x_143 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_144 = lean_ctor_get(x_7, 12);
x_145 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_146 = lean_ctor_get(x_7, 13);
x_147 = lean_nat_dec_eq(x_134, x_135);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; uint8_t x_928; 
lean_inc_ref(x_146);
lean_inc(x_144);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc_ref(x_133);
lean_inc_ref(x_132);
lean_inc_ref(x_131);
x_928 = !lean_is_exclusive(x_7);
if (x_928 == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_929 = lean_ctor_get(x_7, 13);
lean_dec(x_929);
x_930 = lean_ctor_get(x_7, 12);
lean_dec(x_930);
x_931 = lean_ctor_get(x_7, 11);
lean_dec(x_931);
x_932 = lean_ctor_get(x_7, 10);
lean_dec(x_932);
x_933 = lean_ctor_get(x_7, 9);
lean_dec(x_933);
x_934 = lean_ctor_get(x_7, 8);
lean_dec(x_934);
x_935 = lean_ctor_get(x_7, 7);
lean_dec(x_935);
x_936 = lean_ctor_get(x_7, 6);
lean_dec(x_936);
x_937 = lean_ctor_get(x_7, 5);
lean_dec(x_937);
x_938 = lean_ctor_get(x_7, 4);
lean_dec(x_938);
x_939 = lean_ctor_get(x_7, 3);
lean_dec(x_939);
x_940 = lean_ctor_get(x_7, 2);
lean_dec(x_940);
x_941 = lean_ctor_get(x_7, 1);
lean_dec(x_941);
x_942 = lean_ctor_get(x_7, 0);
lean_dec(x_942);
x_148 = x_7;
x_149 = x_928;
goto block_927;
}
else
{
lean_dec(x_7);
x_148 = lean_box(0);
x_149 = x_928;
goto block_927;
}
block_927:
{
lean_object* x_150; 
x_150 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; uint8_t x_917; 
x_917 = !lean_is_exclusive(x_150);
if (x_917 == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_150, 0);
lean_dec(x_918);
x_151 = x_150;
x_152 = x_917;
goto block_916;
}
else
{
lean_dec(x_150);
x_151 = lean_box(0);
x_152 = x_917;
goto block_916;
}
block_916:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_add(x_134, x_227);
lean_inc(x_135);
if (x_149 == 0)
{
lean_ctor_set(x_148, 3, x_228);
x_229 = x_148;
goto block_914;
}
else
{
lean_object* x_915; 
x_915 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_915, 0, x_131);
lean_ctor_set(x_915, 1, x_132);
lean_ctor_set(x_915, 2, x_133);
lean_ctor_set(x_915, 3, x_228);
lean_ctor_set(x_915, 4, x_135);
lean_ctor_set(x_915, 5, x_136);
lean_ctor_set(x_915, 6, x_137);
lean_ctor_set(x_915, 7, x_138);
lean_ctor_set(x_915, 8, x_139);
lean_ctor_set(x_915, 9, x_140);
lean_ctor_set(x_915, 10, x_141);
lean_ctor_set(x_915, 11, x_142);
lean_ctor_set(x_915, 12, x_144);
lean_ctor_set(x_915, 13, x_146);
lean_ctor_set_uint8(x_915, sizeof(void*)*14, x_143);
lean_ctor_set_uint8(x_915, sizeof(void*)*14 + 1, x_145);
x_229 = x_915;
goto block_914;
}
block_226:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_153, 0);
x_163 = lean_ctor_get(x_153, 2);
x_164 = lean_ctor_get(x_153, 3);
x_165 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_162, x_156);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; uint8_t x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = 0;
x_168 = lean_unbox(x_166);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = lean_unbox(x_166);
lean_dec(x_166);
x_101 = x_170;
x_102 = x_154;
x_103 = x_153;
x_104 = x_155;
x_105 = x_156;
x_106 = x_157;
x_107 = x_158;
x_108 = x_159;
x_109 = x_160;
x_110 = x_161;
x_111 = lean_box(0);
goto block_122;
}
else
{
uint8_t x_171; 
lean_inc_ref(x_164);
x_171 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_164, x_163);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = lean_unbox(x_166);
lean_dec(x_166);
x_101 = x_172;
x_102 = x_154;
x_103 = x_153;
x_104 = x_155;
x_105 = x_156;
x_106 = x_157;
x_107 = x_158;
x_108 = x_159;
x_109 = x_160;
x_110 = x_161;
x_111 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_st_ref_get(x_156);
x_174 = lean_ctor_get(x_173, 0);
lean_inc_ref(x_174);
lean_dec(x_173);
x_175 = l_Lean_Compiler_LCNF_normFunDeclImp(x_167, x_147, x_153, x_174, x_158, x_159, x_160, x_161);
lean_dec_ref(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc_ref(x_158);
x_177 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_176, x_158, x_159, x_160, x_161);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_156);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
lean_dec_ref(x_179);
x_180 = lean_unbox(x_166);
lean_dec(x_166);
x_101 = x_180;
x_102 = x_154;
x_103 = x_178;
x_104 = x_155;
x_105 = x_156;
x_106 = x_157;
x_107 = x_158;
x_108 = x_159;
x_109 = x_160;
x_110 = x_161;
x_111 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_188; 
lean_dec(x_178);
lean_dec(x_166);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_179, 0);
x_188 = !lean_is_exclusive(x_179);
if (x_188 == 0)
{
x_182 = x_179;
x_183 = x_188;
goto block_187;
}
else
{
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_box(0);
x_183 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_184; 
if (x_183 == 0)
{
x_184 = x_182;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_181);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_196; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_177, 0);
x_196 = !lean_is_exclusive(x_177);
if (x_196 == 0)
{
x_190 = x_177;
x_191 = x_196;
goto block_195;
}
else
{
lean_inc(x_189);
lean_dec(x_177);
x_190 = lean_box(0);
x_191 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_192; 
if (x_191 == 0)
{
x_192 = x_190;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_189);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_175, 0);
x_204 = !lean_is_exclusive(x_175);
if (x_204 == 0)
{
x_198 = x_175;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_175);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_st_ref_get(x_156);
x_206 = lean_ctor_get(x_205, 0);
lean_inc_ref(x_206);
lean_dec(x_205);
x_207 = l_Lean_Compiler_LCNF_normFunDeclImp(x_167, x_147, x_153, x_206, x_158, x_159, x_160, x_161);
lean_dec_ref(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_unbox(x_166);
lean_dec(x_166);
x_49 = x_209;
x_50 = x_154;
x_51 = x_208;
x_52 = x_155;
x_53 = x_156;
x_54 = x_157;
x_55 = x_158;
x_56 = x_159;
x_57 = x_160;
x_58 = x_161;
x_59 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_217; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_1);
x_210 = lean_ctor_get(x_207, 0);
x_217 = !lean_is_exclusive(x_207);
if (x_217 == 0)
{
x_211 = x_207;
x_212 = x_217;
goto block_216;
}
else
{
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_box(0);
x_212 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_213; 
if (x_212 == 0)
{
x_213 = x_211;
goto block_214;
}
else
{
lean_object* x_215; 
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_210);
x_213 = x_215;
goto block_214;
}
block_214:
{
return x_213;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_225; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_1);
x_218 = lean_ctor_get(x_165, 0);
x_225 = !lean_is_exclusive(x_165);
if (x_225 == 0)
{
x_219 = x_165;
x_220 = x_225;
goto block_224;
}
else
{
lean_inc(x_218);
lean_dec(x_165);
x_219 = lean_box(0);
x_220 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_221; 
if (x_220 == 0)
{
x_221 = x_219;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_218);
x_221 = x_223;
goto block_222;
}
block_222:
{
return x_221;
}
}
}
}
block_914:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_472; 
lean_del_object(x_151);
lean_dec(x_135);
lean_dec(x_134);
x_230 = lean_ctor_get(x_1, 0);
x_231 = lean_ctor_get(x_1, 1);
x_456 = 0;
lean_inc_ref(x_230);
x_472 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_456, x_147, x_230, x_3, x_6);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_527; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
lean_dec_ref(x_472);
lean_inc(x_473);
lean_inc_ref(x_230);
x_527 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_456, x_230, x_473);
if (x_527 == 0)
{
goto block_526;
}
else
{
if (x_147 == 0)
{
x_474 = x_2;
x_475 = x_3;
x_476 = x_4;
x_477 = x_5;
x_478 = x_6;
x_479 = x_229;
x_480 = x_8;
x_481 = lean_box(0);
goto block_516;
}
else
{
goto block_526;
}
}
block_516:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_473, 2);
x_483 = lean_ctor_get(x_473, 3);
lean_inc(x_480);
lean_inc_ref(x_479);
lean_inc(x_478);
lean_inc_ref(x_477);
lean_inc_ref(x_476);
lean_inc(x_483);
x_484 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_483, x_474, x_476, x_477, x_478, x_479, x_480);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec_ref(x_484);
if (lean_obj_tag(x_485) == 1)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
lean_dec_ref(x_485);
x_487 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_475);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; 
lean_dec_ref(x_487);
x_488 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_456, x_473, x_486, x_478);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
lean_dec_ref(x_488);
x_490 = lean_ctor_get(x_489, 2);
lean_inc_ref(x_490);
x_491 = lean_ctor_get(x_489, 3);
lean_inc(x_491);
x_457 = x_489;
x_458 = x_490;
x_459 = x_491;
x_460 = x_474;
x_461 = x_475;
x_462 = x_476;
x_463 = x_477;
x_464 = x_478;
x_465 = x_479;
x_466 = x_480;
x_467 = lean_box(0);
goto block_471;
}
else
{
lean_object* x_492; lean_object* x_493; uint8_t x_494; uint8_t x_499; 
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec_ref(x_476);
lean_dec(x_475);
lean_dec_ref(x_474);
lean_dec_ref(x_1);
x_492 = lean_ctor_get(x_488, 0);
x_499 = !lean_is_exclusive(x_488);
if (x_499 == 0)
{
x_493 = x_488;
x_494 = x_499;
goto block_498;
}
else
{
lean_inc(x_492);
lean_dec(x_488);
x_493 = lean_box(0);
x_494 = x_499;
goto block_498;
}
block_498:
{
lean_object* x_495; 
if (x_494 == 0)
{
x_495 = x_493;
goto block_496;
}
else
{
lean_object* x_497; 
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_492);
x_495 = x_497;
goto block_496;
}
block_496:
{
return x_495;
}
}
}
}
else
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; uint8_t x_507; 
lean_dec(x_486);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec_ref(x_476);
lean_dec(x_475);
lean_dec_ref(x_474);
lean_dec(x_473);
lean_dec_ref(x_1);
x_500 = lean_ctor_get(x_487, 0);
x_507 = !lean_is_exclusive(x_487);
if (x_507 == 0)
{
x_501 = x_487;
x_502 = x_507;
goto block_506;
}
else
{
lean_inc(x_500);
lean_dec(x_487);
x_501 = lean_box(0);
x_502 = x_507;
goto block_506;
}
block_506:
{
lean_object* x_503; 
if (x_502 == 0)
{
x_503 = x_501;
goto block_504;
}
else
{
lean_object* x_505; 
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_500);
x_503 = x_505;
goto block_504;
}
block_504:
{
return x_503;
}
}
}
}
else
{
lean_inc(x_483);
lean_inc_ref(x_482);
lean_dec(x_485);
x_457 = x_473;
x_458 = x_482;
x_459 = x_483;
x_460 = x_474;
x_461 = x_475;
x_462 = x_476;
x_463 = x_477;
x_464 = x_478;
x_465 = x_479;
x_466 = x_480;
x_467 = lean_box(0);
goto block_471;
}
}
else
{
lean_object* x_508; lean_object* x_509; uint8_t x_510; uint8_t x_515; 
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec_ref(x_477);
lean_dec_ref(x_476);
lean_dec(x_475);
lean_dec_ref(x_474);
lean_dec(x_473);
lean_dec_ref(x_1);
x_508 = lean_ctor_get(x_484, 0);
x_515 = !lean_is_exclusive(x_484);
if (x_515 == 0)
{
x_509 = x_484;
x_510 = x_515;
goto block_514;
}
else
{
lean_inc(x_508);
lean_dec(x_484);
x_509 = lean_box(0);
x_510 = x_515;
goto block_514;
}
block_514:
{
lean_object* x_511; 
if (x_510 == 0)
{
x_511 = x_509;
goto block_512;
}
else
{
lean_object* x_513; 
x_513 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_513, 0, x_508);
x_511 = x_513;
goto block_512;
}
block_512:
{
return x_511;
}
}
}
}
block_526:
{
lean_object* x_517; 
x_517 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_517) == 0)
{
lean_dec_ref(x_517);
x_474 = x_2;
x_475 = x_3;
x_476 = x_4;
x_477 = x_5;
x_478 = x_6;
x_479 = x_229;
x_480 = x_8;
x_481 = lean_box(0);
goto block_516;
}
else
{
lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_525; 
lean_dec(x_473);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_518 = lean_ctor_get(x_517, 0);
x_525 = !lean_is_exclusive(x_517);
if (x_525 == 0)
{
x_519 = x_517;
x_520 = x_525;
goto block_524;
}
else
{
lean_inc(x_518);
lean_dec(x_517);
x_519 = lean_box(0);
x_520 = x_525;
goto block_524;
}
block_524:
{
lean_object* x_521; 
if (x_520 == 0)
{
x_521 = x_519;
goto block_522;
}
else
{
lean_object* x_523; 
x_523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_523, 0, x_518);
x_521 = x_523;
goto block_522;
}
block_522:
{
return x_521;
}
}
}
}
}
else
{
lean_object* x_528; lean_object* x_529; uint8_t x_530; uint8_t x_535; 
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_528 = lean_ctor_get(x_472, 0);
x_535 = !lean_is_exclusive(x_472);
if (x_535 == 0)
{
x_529 = x_472;
x_530 = x_535;
goto block_534;
}
else
{
lean_inc(x_528);
lean_dec(x_472);
x_529 = lean_box(0);
x_530 = x_535;
goto block_534;
}
block_534:
{
lean_object* x_531; 
if (x_530 == 0)
{
x_531 = x_529;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_528);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
}
block_455:
{
if (x_241 == 0)
{
lean_object* x_242; 
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_235);
x_242 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_235, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
if (lean_obj_tag(x_243) == 1)
{
lean_object* x_244; lean_object* x_245; 
lean_inc_ref(x_231);
lean_dec_ref(x_235);
lean_dec_ref(x_1);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_232);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
lean_dec_ref(x_245);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
lean_inc_ref(x_234);
x_246 = l_Lean_Compiler_LCNF_Simp_simp(x_231, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_244, x_247, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
lean_dec(x_233);
lean_dec_ref(x_236);
lean_dec(x_237);
lean_dec_ref(x_238);
lean_dec_ref(x_239);
lean_dec(x_232);
lean_dec_ref(x_234);
lean_dec(x_244);
return x_248;
}
else
{
lean_dec(x_244);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
return x_246;
}
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_256; 
lean_dec(x_244);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_249 = lean_ctor_get(x_245, 0);
x_256 = !lean_is_exclusive(x_245);
if (x_256 == 0)
{
x_250 = x_245;
x_251 = x_256;
goto block_255;
}
else
{
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_box(0);
x_251 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_252; 
if (x_251 == 0)
{
x_252 = x_250;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_249);
x_252 = x_254;
goto block_253;
}
block_253:
{
return x_252;
}
}
}
}
else
{
lean_object* x_257; 
lean_dec(x_243);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_235);
x_257 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_235, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
if (lean_obj_tag(x_258) == 1)
{
lean_object* x_259; uint8_t x_260; uint8_t x_267; 
lean_inc_ref(x_231);
lean_dec_ref(x_235);
x_267 = !lean_is_exclusive(x_1);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_1, 1);
lean_dec(x_268);
x_269 = lean_ctor_get(x_1, 0);
lean_dec(x_269);
x_259 = x_1;
x_260 = x_267;
goto block_266;
}
else
{
lean_dec(x_1);
x_259 = lean_box(0);
x_260 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_261);
lean_dec_ref(x_258);
if (x_260 == 0)
{
lean_ctor_set_tag(x_259, 1);
lean_ctor_set(x_259, 0, x_261);
x_262 = x_259;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_261);
lean_ctor_set(x_265, 1, x_231);
x_262 = x_265;
goto block_264;
}
block_264:
{
x_1 = x_262;
x_2 = x_234;
x_3 = x_232;
x_4 = x_239;
x_5 = x_238;
x_6 = x_237;
x_7 = x_236;
x_8 = x_233;
goto _start;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_258);
x_270 = lean_ctor_get(x_235, 0);
x_271 = lean_ctor_get(x_235, 3);
x_272 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
if (lean_obj_tag(x_273) == 1)
{
lean_object* x_274; lean_object* x_275; 
lean_inc_ref(x_231);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
lean_inc(x_270);
x_275 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_270, x_274, x_232, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
lean_dec_ref(x_275);
x_276 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_235, x_232, x_237);
lean_dec_ref(x_235);
if (lean_obj_tag(x_276) == 0)
{
lean_dec_ref(x_276);
x_1 = x_231;
x_2 = x_234;
x_3 = x_232;
x_4 = x_239;
x_5 = x_238;
x_6 = x_237;
x_7 = x_236;
x_8 = x_233;
goto _start;
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_285; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_278 = lean_ctor_get(x_276, 0);
x_285 = !lean_is_exclusive(x_276);
if (x_285 == 0)
{
x_279 = x_276;
x_280 = x_285;
goto block_284;
}
else
{
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_box(0);
x_280 = x_285;
goto block_284;
}
block_284:
{
lean_object* x_281; 
if (x_280 == 0)
{
x_281 = x_279;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_278);
x_281 = x_283;
goto block_282;
}
block_282:
{
return x_281;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_293; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_286 = lean_ctor_get(x_275, 0);
x_293 = !lean_is_exclusive(x_275);
if (x_293 == 0)
{
x_287 = x_275;
x_288 = x_293;
goto block_292;
}
else
{
lean_inc(x_286);
lean_dec(x_275);
x_287 = lean_box(0);
x_288 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_289; 
if (x_288 == 0)
{
x_289 = x_287;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_286);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
else
{
lean_object* x_294; 
lean_dec(x_273);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
lean_inc_ref(x_234);
lean_inc_ref(x_231);
lean_inc_ref(x_235);
x_294 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_235, x_231, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
if (lean_obj_tag(x_295) == 1)
{
lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec_ref(x_1);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_235, x_232, x_237);
lean_dec(x_237);
lean_dec(x_232);
lean_dec_ref(x_235);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; uint8_t x_299; uint8_t x_304; 
x_304 = !lean_is_exclusive(x_297);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_297, 0);
lean_dec(x_305);
x_298 = x_297;
x_299 = x_304;
goto block_303;
}
else
{
lean_dec(x_297);
x_298 = lean_box(0);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_299 == 0)
{
lean_ctor_set(x_298, 0, x_296);
x_300 = x_298;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_296);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_313; 
lean_dec(x_296);
x_306 = lean_ctor_get(x_297, 0);
x_313 = !lean_is_exclusive(x_297);
if (x_313 == 0)
{
x_307 = x_297;
x_308 = x_313;
goto block_312;
}
else
{
lean_inc(x_306);
lean_dec(x_297);
x_307 = lean_box(0);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_308 == 0)
{
x_309 = x_307;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_306);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
}
else
{
lean_object* x_314; 
lean_dec(x_295);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
lean_inc_ref(x_234);
lean_inc(x_271);
x_314 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_271, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec_ref(x_314);
if (lean_obj_tag(x_315) == 1)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_inc_ref(x_231);
lean_dec_ref(x_1);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
lean_inc(x_270);
x_319 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_270, x_318, x_232, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
lean_dec_ref(x_319);
x_320 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_235, x_232, x_237);
lean_dec_ref(x_235);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; 
lean_dec_ref(x_320);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
lean_inc_ref(x_234);
x_321 = l_Lean_Compiler_LCNF_Simp_simp(x_231, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec_ref(x_321);
x_323 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_317, x_322, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
lean_dec(x_233);
lean_dec_ref(x_236);
lean_dec(x_237);
lean_dec_ref(x_238);
lean_dec_ref(x_239);
lean_dec(x_232);
lean_dec_ref(x_234);
lean_dec(x_317);
return x_323;
}
else
{
lean_dec(x_317);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
return x_321;
}
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_331; 
lean_dec(x_317);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_324 = lean_ctor_get(x_320, 0);
x_331 = !lean_is_exclusive(x_320);
if (x_331 == 0)
{
x_325 = x_320;
x_326 = x_331;
goto block_330;
}
else
{
lean_inc(x_324);
lean_dec(x_320);
x_325 = lean_box(0);
x_326 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_327; 
if (x_326 == 0)
{
x_327 = x_325;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_324);
x_327 = x_329;
goto block_328;
}
block_328:
{
return x_327;
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_339; 
lean_dec(x_317);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_332 = lean_ctor_get(x_319, 0);
x_339 = !lean_is_exclusive(x_319);
if (x_339 == 0)
{
x_333 = x_319;
x_334 = x_339;
goto block_338;
}
else
{
lean_inc(x_332);
lean_dec(x_319);
x_333 = lean_box(0);
x_334 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_335; 
if (x_334 == 0)
{
x_335 = x_333;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_332);
x_335 = x_337;
goto block_336;
}
block_336:
{
return x_335;
}
}
}
}
else
{
lean_object* x_340; 
lean_dec(x_315);
lean_inc(x_233);
lean_inc_ref(x_236);
lean_inc(x_237);
lean_inc_ref(x_238);
lean_inc_ref(x_239);
lean_inc(x_232);
lean_inc_ref(x_234);
lean_inc_ref(x_231);
x_340 = l_Lean_Compiler_LCNF_Simp_simp(x_231, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_270, x_232);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = lean_unbox(x_343);
lean_dec(x_343);
if (x_344 == 0)
{
lean_object* x_345; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec_ref(x_1);
x_345 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_235, x_232, x_237);
lean_dec(x_237);
lean_dec(x_232);
lean_dec_ref(x_235);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; uint8_t x_347; uint8_t x_352; 
x_352 = !lean_is_exclusive(x_345);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_345, 0);
lean_dec(x_353);
x_346 = x_345;
x_347 = x_352;
goto block_351;
}
else
{
lean_dec(x_345);
x_346 = lean_box(0);
x_347 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_348; 
if (x_347 == 0)
{
lean_ctor_set(x_346, 0, x_341);
x_348 = x_346;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_350, 0, x_341);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; uint8_t x_361; 
lean_dec(x_341);
x_354 = lean_ctor_get(x_345, 0);
x_361 = !lean_is_exclusive(x_345);
if (x_361 == 0)
{
x_355 = x_345;
x_356 = x_361;
goto block_360;
}
else
{
lean_inc(x_354);
lean_dec(x_345);
x_355 = lean_box(0);
x_356 = x_361;
goto block_360;
}
block_360:
{
lean_object* x_357; 
if (x_356 == 0)
{
x_357 = x_355;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_354);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
}
}
else
{
lean_object* x_362; 
lean_inc_ref(x_235);
x_362 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_235, x_234, x_232, x_239, x_238, x_237, x_236, x_233);
lean_dec(x_233);
lean_dec_ref(x_236);
lean_dec(x_237);
lean_dec_ref(x_238);
lean_dec_ref(x_239);
lean_dec(x_232);
lean_dec_ref(x_234);
if (lean_obj_tag(x_362) == 0)
{
size_t x_363; size_t x_364; uint8_t x_365; 
lean_dec_ref(x_362);
x_363 = lean_ptr_addr(x_231);
x_364 = lean_ptr_addr(x_341);
x_365 = lean_usize_dec_eq(x_363, x_364);
if (x_365 == 0)
{
x_123 = x_235;
x_124 = lean_box(0);
x_125 = x_341;
x_126 = x_365;
goto block_130;
}
else
{
size_t x_366; size_t x_367; uint8_t x_368; 
x_366 = lean_ptr_addr(x_230);
x_367 = lean_ptr_addr(x_235);
x_368 = lean_usize_dec_eq(x_366, x_367);
x_123 = x_235;
x_124 = lean_box(0);
x_125 = x_341;
x_126 = x_368;
goto block_130;
}
}
else
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; uint8_t x_376; 
lean_dec(x_341);
lean_dec_ref(x_235);
lean_dec_ref(x_1);
x_369 = lean_ctor_get(x_362, 0);
x_376 = !lean_is_exclusive(x_362);
if (x_376 == 0)
{
x_370 = x_362;
x_371 = x_376;
goto block_375;
}
else
{
lean_inc(x_369);
lean_dec(x_362);
x_370 = lean_box(0);
x_371 = x_376;
goto block_375;
}
block_375:
{
lean_object* x_372; 
if (x_371 == 0)
{
x_372 = x_370;
goto block_373;
}
else
{
lean_object* x_374; 
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_369);
x_372 = x_374;
goto block_373;
}
block_373:
{
return x_372;
}
}
}
}
}
else
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; uint8_t x_384; 
lean_dec(x_341);
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_377 = lean_ctor_get(x_342, 0);
x_384 = !lean_is_exclusive(x_342);
if (x_384 == 0)
{
x_378 = x_342;
x_379 = x_384;
goto block_383;
}
else
{
lean_inc(x_377);
lean_dec(x_342);
x_378 = lean_box(0);
x_379 = x_384;
goto block_383;
}
block_383:
{
lean_object* x_380; 
if (x_379 == 0)
{
x_380 = x_378;
goto block_381;
}
else
{
lean_object* x_382; 
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_377);
x_380 = x_382;
goto block_381;
}
block_381:
{
return x_380;
}
}
}
}
else
{
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
return x_340;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; uint8_t x_392; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_385 = lean_ctor_get(x_314, 0);
x_392 = !lean_is_exclusive(x_314);
if (x_392 == 0)
{
x_386 = x_314;
x_387 = x_392;
goto block_391;
}
else
{
lean_inc(x_385);
lean_dec(x_314);
x_386 = lean_box(0);
x_387 = x_392;
goto block_391;
}
block_391:
{
lean_object* x_388; 
if (x_387 == 0)
{
x_388 = x_386;
goto block_389;
}
else
{
lean_object* x_390; 
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_385);
x_388 = x_390;
goto block_389;
}
block_389:
{
return x_388;
}
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_400; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_393 = lean_ctor_get(x_294, 0);
x_400 = !lean_is_exclusive(x_294);
if (x_400 == 0)
{
x_394 = x_294;
x_395 = x_400;
goto block_399;
}
else
{
lean_inc(x_393);
lean_dec(x_294);
x_394 = lean_box(0);
x_395 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_396; 
if (x_395 == 0)
{
x_396 = x_394;
goto block_397;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_393);
x_396 = x_398;
goto block_397;
}
block_397:
{
return x_396;
}
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_408; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_401 = lean_ctor_get(x_272, 0);
x_408 = !lean_is_exclusive(x_272);
if (x_408 == 0)
{
x_402 = x_272;
x_403 = x_408;
goto block_407;
}
else
{
lean_inc(x_401);
lean_dec(x_272);
x_402 = lean_box(0);
x_403 = x_408;
goto block_407;
}
block_407:
{
lean_object* x_404; 
if (x_403 == 0)
{
x_404 = x_402;
goto block_405;
}
else
{
lean_object* x_406; 
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_401);
x_404 = x_406;
goto block_405;
}
block_405:
{
return x_404;
}
}
}
}
}
else
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; uint8_t x_416; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_409 = lean_ctor_get(x_257, 0);
x_416 = !lean_is_exclusive(x_257);
if (x_416 == 0)
{
x_410 = x_257;
x_411 = x_416;
goto block_415;
}
else
{
lean_inc(x_409);
lean_dec(x_257);
x_410 = lean_box(0);
x_411 = x_416;
goto block_415;
}
block_415:
{
lean_object* x_412; 
if (x_411 == 0)
{
x_412 = x_410;
goto block_413;
}
else
{
lean_object* x_414; 
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_409);
x_412 = x_414;
goto block_413;
}
block_413:
{
return x_412;
}
}
}
}
}
else
{
lean_object* x_417; lean_object* x_418; uint8_t x_419; uint8_t x_424; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_417 = lean_ctor_get(x_242, 0);
x_424 = !lean_is_exclusive(x_242);
if (x_424 == 0)
{
x_418 = x_242;
x_419 = x_424;
goto block_423;
}
else
{
lean_inc(x_417);
lean_dec(x_242);
x_418 = lean_box(0);
x_419 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_420; 
if (x_419 == 0)
{
x_420 = x_418;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_417);
x_420 = x_422;
goto block_421;
}
block_421:
{
return x_420;
}
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; uint8_t x_454; 
lean_inc_ref(x_231);
lean_dec_ref(x_1);
x_425 = lean_st_ref_take(x_232);
x_426 = lean_ctor_get(x_235, 0);
x_427 = lean_ctor_get(x_425, 0);
x_428 = lean_ctor_get(x_425, 1);
x_429 = lean_ctor_get(x_425, 2);
x_430 = lean_ctor_get(x_425, 3);
x_431 = lean_ctor_get_uint8(x_425, sizeof(void*)*7);
x_432 = lean_ctor_get(x_425, 4);
x_433 = lean_ctor_get(x_425, 5);
x_434 = lean_ctor_get(x_425, 6);
x_454 = !lean_is_exclusive(x_425);
if (x_454 == 0)
{
x_435 = x_425;
x_436 = x_454;
goto block_453;
}
else
{
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_425);
x_435 = lean_box(0);
x_436 = x_454;
goto block_453;
}
block_453:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_box(0);
lean_inc(x_426);
x_438 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_427, x_426, x_437);
if (x_436 == 0)
{
lean_ctor_set(x_435, 0, x_438);
x_439 = x_435;
goto block_451;
}
else
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_452, 0, x_438);
lean_ctor_set(x_452, 1, x_428);
lean_ctor_set(x_452, 2, x_429);
lean_ctor_set(x_452, 3, x_430);
lean_ctor_set(x_452, 4, x_432);
lean_ctor_set(x_452, 5, x_433);
lean_ctor_set(x_452, 6, x_434);
lean_ctor_set_uint8(x_452, sizeof(void*)*7, x_431);
x_439 = x_452;
goto block_451;
}
block_451:
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_st_ref_set(x_232, x_439);
x_441 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_235, x_232, x_237);
lean_dec_ref(x_235);
if (lean_obj_tag(x_441) == 0)
{
lean_dec_ref(x_441);
x_1 = x_231;
x_2 = x_234;
x_3 = x_232;
x_4 = x_239;
x_5 = x_238;
x_6 = x_237;
x_7 = x_236;
x_8 = x_233;
goto _start;
}
else
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; uint8_t x_450; 
lean_dec_ref(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
x_443 = lean_ctor_get(x_441, 0);
x_450 = !lean_is_exclusive(x_441);
if (x_450 == 0)
{
x_444 = x_441;
x_445 = x_450;
goto block_449;
}
else
{
lean_inc(x_443);
lean_dec(x_441);
x_444 = lean_box(0);
x_445 = x_450;
goto block_449;
}
block_449:
{
lean_object* x_446; 
if (x_445 == 0)
{
x_446 = x_444;
goto block_447;
}
else
{
lean_object* x_448; 
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_443);
x_446 = x_448;
goto block_447;
}
block_447:
{
return x_446;
}
}
}
}
}
}
}
block_471:
{
uint8_t x_468; 
x_468 = l_Lean_Expr_isErased(x_458);
lean_dec_ref(x_458);
if (x_468 == 0)
{
lean_dec(x_459);
x_232 = x_461;
x_233 = x_466;
x_234 = x_460;
x_235 = x_457;
x_236 = x_465;
x_237 = x_464;
x_238 = x_463;
x_239 = x_462;
x_240 = lean_box(0);
x_241 = x_147;
goto block_455;
}
else
{
lean_object* x_469; uint8_t x_470; 
x_469 = lean_box(1);
x_470 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_456, x_459, x_469);
if (x_470 == 0)
{
x_232 = x_461;
x_233 = x_466;
x_234 = x_460;
x_235 = x_457;
x_236 = x_465;
x_237 = x_464;
x_238 = x_463;
x_239 = x_462;
x_240 = lean_box(0);
x_241 = x_468;
goto block_455;
}
else
{
x_232 = x_461;
x_233 = x_466;
x_234 = x_460;
x_235 = x_457;
x_236 = x_465;
x_237 = x_464;
x_238 = x_463;
x_239 = x_462;
x_240 = lean_box(0);
x_241 = x_147;
goto block_455;
}
}
}
}
case 3:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
lean_del_object(x_151);
lean_dec(x_135);
lean_dec(x_134);
x_536 = lean_ctor_get(x_1, 0);
x_537 = lean_ctor_get(x_1, 1);
x_538 = lean_st_ref_get(x_3);
x_539 = lean_ctor_get(x_538, 0);
lean_inc_ref(x_539);
lean_dec(x_538);
x_540 = 0;
lean_inc(x_536);
x_541 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_539, x_536, x_147);
lean_dec_ref(x_539);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
lean_dec_ref(x_541);
lean_inc_ref(x_537);
x_543 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_540, x_147, x_537, x_3);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; uint8_t x_546; uint8_t x_614; 
x_544 = lean_ctor_get(x_543, 0);
x_614 = !lean_is_exclusive(x_543);
if (x_614 == 0)
{
x_545 = x_543;
x_546 = x_614;
goto block_613;
}
else
{
lean_inc(x_544);
lean_dec(x_543);
x_545 = lean_box(0);
x_546 = x_614;
goto block_613;
}
block_613:
{
lean_object* x_547; uint8_t x_548; lean_object* x_565; lean_object* x_571; lean_object* x_581; 
lean_inc(x_8);
lean_inc_ref(x_229);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_544);
x_581 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_542, x_544, x_2, x_3, x_4, x_5, x_6, x_229, x_8);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
lean_dec_ref(x_581);
if (lean_obj_tag(x_582) == 1)
{
lean_object* x_583; 
lean_del_object(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec_ref(x_1);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
lean_dec_ref(x_582);
x_1 = x_583;
x_7 = x_229;
goto _start;
}
else
{
lean_object* x_585; 
lean_dec(x_582);
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_542);
x_585 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_542, x_3);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; uint8_t x_588; 
lean_dec_ref(x_585);
x_586 = lean_unsigned_to_nat(0u);
x_587 = lean_array_get_size(x_544);
x_588 = lean_nat_dec_lt(x_586, x_587);
if (x_588 == 0)
{
lean_dec(x_3);
x_565 = lean_box(0);
goto block_570;
}
else
{
lean_object* x_589; uint8_t x_590; 
x_589 = lean_box(0);
x_590 = lean_nat_dec_le(x_587, x_587);
if (x_590 == 0)
{
if (x_588 == 0)
{
lean_dec(x_3);
x_565 = lean_box(0);
goto block_570;
}
else
{
size_t x_591; size_t x_592; lean_object* x_593; 
x_591 = 0;
x_592 = lean_usize_of_nat(x_587);
x_593 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_544, x_591, x_592, x_589, x_3);
lean_dec(x_3);
x_571 = x_593;
goto block_580;
}
}
else
{
size_t x_594; size_t x_595; lean_object* x_596; 
x_594 = 0;
x_595 = lean_usize_of_nat(x_587);
x_596 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_544, x_594, x_595, x_589, x_3);
lean_dec(x_3);
x_571 = x_596;
goto block_580;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; uint8_t x_599; uint8_t x_604; 
lean_del_object(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec_ref(x_1);
lean_dec(x_3);
x_597 = lean_ctor_get(x_585, 0);
x_604 = !lean_is_exclusive(x_585);
if (x_604 == 0)
{
x_598 = x_585;
x_599 = x_604;
goto block_603;
}
else
{
lean_inc(x_597);
lean_dec(x_585);
x_598 = lean_box(0);
x_599 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_600; 
if (x_599 == 0)
{
x_600 = x_598;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_597);
x_600 = x_602;
goto block_601;
}
block_601:
{
return x_600;
}
}
}
}
}
else
{
lean_object* x_605; lean_object* x_606; uint8_t x_607; uint8_t x_612; 
lean_del_object(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_605 = lean_ctor_get(x_581, 0);
x_612 = !lean_is_exclusive(x_581);
if (x_612 == 0)
{
x_606 = x_581;
x_607 = x_612;
goto block_611;
}
else
{
lean_inc(x_605);
lean_dec(x_581);
x_606 = lean_box(0);
x_607 = x_612;
goto block_611;
}
block_611:
{
lean_object* x_608; 
if (x_607 == 0)
{
x_608 = x_606;
goto block_609;
}
else
{
lean_object* x_610; 
x_610 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_610, 0, x_605);
x_608 = x_610;
goto block_609;
}
block_609:
{
return x_608;
}
}
}
block_564:
{
if (x_548 == 0)
{
lean_object* x_549; uint8_t x_550; uint8_t x_558; 
x_558 = !lean_is_exclusive(x_1);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_1, 1);
lean_dec(x_559);
x_560 = lean_ctor_get(x_1, 0);
lean_dec(x_560);
x_549 = x_1;
x_550 = x_558;
goto block_557;
}
else
{
lean_dec(x_1);
x_549 = lean_box(0);
x_550 = x_558;
goto block_557;
}
block_557:
{
lean_object* x_551; 
if (x_550 == 0)
{
lean_ctor_set(x_549, 1, x_544);
lean_ctor_set(x_549, 0, x_542);
x_551 = x_549;
goto block_555;
}
else
{
lean_object* x_556; 
x_556 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_556, 0, x_542);
lean_ctor_set(x_556, 1, x_544);
x_551 = x_556;
goto block_555;
}
block_555:
{
lean_object* x_552; 
if (x_546 == 0)
{
lean_ctor_set(x_545, 0, x_551);
x_552 = x_545;
goto block_553;
}
else
{
lean_object* x_554; 
x_554 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_554, 0, x_551);
x_552 = x_554;
goto block_553;
}
block_553:
{
return x_552;
}
}
}
}
else
{
lean_object* x_561; 
lean_dec(x_544);
lean_dec(x_542);
if (x_546 == 0)
{
lean_ctor_set(x_545, 0, x_1);
x_561 = x_545;
goto block_562;
}
else
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_563, 0, x_1);
x_561 = x_563;
goto block_562;
}
block_562:
{
return x_561;
}
}
}
block_570:
{
uint8_t x_566; 
x_566 = l_Lean_instBEqFVarId_beq(x_536, x_542);
if (x_566 == 0)
{
x_547 = lean_box(0);
x_548 = x_566;
goto block_564;
}
else
{
size_t x_567; size_t x_568; uint8_t x_569; 
x_567 = lean_ptr_addr(x_537);
x_568 = lean_ptr_addr(x_544);
x_569 = lean_usize_dec_eq(x_567, x_568);
x_547 = lean_box(0);
x_548 = x_569;
goto block_564;
}
}
block_580:
{
if (lean_obj_tag(x_571) == 0)
{
lean_dec_ref(x_571);
x_565 = lean_box(0);
goto block_570;
}
else
{
lean_object* x_572; lean_object* x_573; uint8_t x_574; uint8_t x_579; 
lean_del_object(x_545);
lean_dec(x_544);
lean_dec(x_542);
lean_dec_ref(x_1);
x_572 = lean_ctor_get(x_571, 0);
x_579 = !lean_is_exclusive(x_571);
if (x_579 == 0)
{
x_573 = x_571;
x_574 = x_579;
goto block_578;
}
else
{
lean_inc(x_572);
lean_dec(x_571);
x_573 = lean_box(0);
x_574 = x_579;
goto block_578;
}
block_578:
{
lean_object* x_575; 
if (x_574 == 0)
{
x_575 = x_573;
goto block_576;
}
else
{
lean_object* x_577; 
x_577 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_577, 0, x_572);
x_575 = x_577;
goto block_576;
}
block_576:
{
return x_575;
}
}
}
}
}
}
else
{
lean_object* x_615; lean_object* x_616; uint8_t x_617; uint8_t x_622; 
lean_dec(x_542);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_615 = lean_ctor_get(x_543, 0);
x_622 = !lean_is_exclusive(x_543);
if (x_622 == 0)
{
x_616 = x_543;
x_617 = x_622;
goto block_621;
}
else
{
lean_inc(x_615);
lean_dec(x_543);
x_616 = lean_box(0);
x_617 = x_622;
goto block_621;
}
block_621:
{
lean_object* x_618; 
if (x_617 == 0)
{
x_618 = x_616;
goto block_619;
}
else
{
lean_object* x_620; 
x_620 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_620, 0, x_615);
x_618 = x_620;
goto block_619;
}
block_619:
{
return x_618;
}
}
}
}
else
{
lean_object* x_623; 
lean_dec_ref(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_623 = l_Lean_Compiler_LCNF_mkReturnErased(x_540, x_5, x_6, x_229, x_8);
lean_dec(x_8);
lean_dec_ref(x_229);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_623;
}
}
case 4:
{
lean_object* x_624; lean_object* x_625; 
lean_del_object(x_151);
x_624 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_624);
lean_inc(x_8);
lean_inc_ref(x_229);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_624);
x_625 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_624, x_2, x_3, x_4, x_5, x_6, x_229, x_8);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; uint8_t x_628; uint8_t x_845; 
x_626 = lean_ctor_get(x_625, 0);
x_845 = !lean_is_exclusive(x_625);
if (x_845 == 0)
{
x_627 = x_625;
x_628 = x_845;
goto block_844;
}
else
{
lean_inc(x_626);
lean_dec(x_625);
x_627 = lean_box(0);
x_628 = x_845;
goto block_844;
}
block_844:
{
if (lean_obj_tag(x_626) == 1)
{
lean_object* x_629; lean_object* x_630; 
lean_dec_ref(x_624);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
lean_dec_ref(x_626);
if (x_628 == 0)
{
lean_ctor_set(x_627, 0, x_629);
x_630 = x_627;
goto block_631;
}
else
{
lean_object* x_632; 
x_632 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_632, 0, x_629);
x_630 = x_632;
goto block_631;
}
block_631:
{
return x_630;
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; uint8_t x_843; 
lean_dec(x_626);
x_633 = lean_ctor_get(x_624, 0);
x_634 = lean_ctor_get(x_624, 1);
x_635 = lean_ctor_get(x_624, 2);
x_636 = lean_ctor_get(x_624, 3);
x_843 = !lean_is_exclusive(x_624);
if (x_843 == 0)
{
x_637 = x_624;
x_638 = x_843;
goto block_842;
}
else
{
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_624);
x_637 = lean_box(0);
x_638 = x_843;
goto block_842;
}
block_842:
{
lean_object* x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; 
x_639 = lean_st_ref_get(x_3);
x_640 = lean_ctor_get(x_639, 0);
lean_inc_ref(x_640);
lean_dec(x_639);
x_641 = 0;
lean_inc(x_635);
x_642 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_640, x_635, x_147);
lean_dec_ref(x_640);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; uint8_t x_645; uint8_t x_840; 
x_643 = lean_ctor_get(x_642, 0);
x_840 = !lean_is_exclusive(x_642);
if (x_840 == 0)
{
x_644 = x_642;
x_645 = x_840;
goto block_839;
}
else
{
lean_inc(x_643);
lean_dec(x_642);
x_644 = lean_box(0);
x_645 = x_840;
goto block_839;
}
block_839:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_st_ref_get(x_3);
x_647 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_229);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_636);
lean_inc(x_643);
x_648 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_643, x_134, x_135, x_647, x_636, x_2, x_3, x_4, x_5, x_6, x_229, x_8);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; uint8_t x_651; uint8_t x_830; 
x_649 = lean_ctor_get(x_648, 0);
x_830 = !lean_is_exclusive(x_648);
if (x_830 == 0)
{
x_650 = x_648;
x_651 = x_830;
goto block_829;
}
else
{
lean_inc(x_649);
lean_dec(x_648);
x_650 = lean_box(0);
x_651 = x_830;
goto block_829;
}
block_829:
{
lean_object* x_652; 
lean_inc(x_8);
lean_inc_ref(x_229);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_652 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_649, x_2, x_3, x_4, x_5, x_6, x_229, x_8);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_820; 
x_653 = lean_ctor_get(x_652, 0);
x_820 = !lean_is_exclusive(x_652);
if (x_820 == 0)
{
x_654 = x_652;
x_655 = x_820;
goto block_819;
}
else
{
lean_inc(x_653);
lean_dec(x_652);
x_654 = lean_box(0);
x_655 = x_820;
goto block_819;
}
block_819:
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_681; lean_object* x_682; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_709; lean_object* x_718; uint8_t x_719; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_752; uint8_t x_753; 
x_656 = lean_ctor_get(x_646, 0);
lean_inc_ref(x_656);
lean_dec(x_646);
lean_inc_ref(x_634);
x_657 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_641, x_656, x_147, x_634);
lean_dec_ref(x_656);
x_752 = lean_array_get_size(x_653);
x_753 = lean_nat_dec_eq(x_752, x_227);
if (x_753 == 0)
{
lean_del_object(x_627);
x_725 = x_3;
x_726 = x_5;
x_727 = x_6;
x_728 = x_229;
x_729 = x_8;
x_730 = lean_box(0);
goto block_751;
}
else
{
lean_object* x_754; 
x_754 = lean_array_fget_borrowed(x_653, x_647);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_776; lean_object* x_786; lean_object* x_787; uint8_t x_798; lean_object* x_799; uint8_t x_801; 
lean_del_object(x_627);
x_755 = lean_ctor_get(x_754, 1);
x_756 = lean_ctor_get(x_754, 2);
x_786 = lean_array_get_size(x_755);
x_801 = lean_nat_dec_lt(x_647, x_786);
if (x_801 == 0)
{
x_798 = x_147;
x_799 = lean_box(0);
goto block_800;
}
else
{
if (x_801 == 0)
{
x_798 = x_147;
x_799 = lean_box(0);
goto block_800;
}
else
{
size_t x_802; size_t x_803; lean_object* x_804; 
x_802 = 0;
x_803 = lean_usize_of_nat(x_786);
x_804 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(x_755, x_802, x_803, x_3);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; uint8_t x_806; 
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
lean_dec_ref(x_804);
x_806 = lean_unbox(x_805);
lean_dec(x_805);
x_798 = x_806;
x_799 = lean_box(0);
goto block_800;
}
else
{
lean_object* x_807; lean_object* x_808; uint8_t x_809; uint8_t x_814; 
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_del_object(x_650);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_807 = lean_ctor_get(x_804, 0);
x_814 = !lean_is_exclusive(x_804);
if (x_814 == 0)
{
x_808 = x_804;
x_809 = x_814;
goto block_813;
}
else
{
lean_inc(x_807);
lean_dec(x_804);
x_808 = lean_box(0);
x_809 = x_814;
goto block_813;
}
block_813:
{
lean_object* x_810; 
if (x_809 == 0)
{
x_810 = x_808;
goto block_811;
}
else
{
lean_object* x_812; 
x_812 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_812, 0, x_807);
x_810 = x_812;
goto block_811;
}
block_811:
{
return x_810;
}
}
}
}
}
block_775:
{
lean_object* x_758; 
x_758 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; uint8_t x_760; uint8_t x_765; 
x_765 = !lean_is_exclusive(x_758);
if (x_765 == 0)
{
lean_object* x_766; 
x_766 = lean_ctor_get(x_758, 0);
lean_dec(x_766);
x_759 = x_758;
x_760 = x_765;
goto block_764;
}
else
{
lean_dec(x_758);
x_759 = lean_box(0);
x_760 = x_765;
goto block_764;
}
block_764:
{
lean_object* x_761; 
if (x_760 == 0)
{
lean_ctor_set(x_759, 0, x_756);
x_761 = x_759;
goto block_762;
}
else
{
lean_object* x_763; 
x_763 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_763, 0, x_756);
x_761 = x_763;
goto block_762;
}
block_762:
{
return x_761;
}
}
}
else
{
lean_object* x_767; lean_object* x_768; uint8_t x_769; uint8_t x_774; 
lean_dec_ref(x_756);
x_767 = lean_ctor_get(x_758, 0);
x_774 = !lean_is_exclusive(x_758);
if (x_774 == 0)
{
x_768 = x_758;
x_769 = x_774;
goto block_773;
}
else
{
lean_inc(x_767);
lean_dec(x_758);
x_768 = lean_box(0);
x_769 = x_774;
goto block_773;
}
block_773:
{
lean_object* x_770; 
if (x_769 == 0)
{
x_770 = x_768;
goto block_771;
}
else
{
lean_object* x_772; 
x_772 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_772, 0, x_767);
x_770 = x_772;
goto block_771;
}
block_771:
{
return x_770;
}
}
}
}
block_785:
{
if (lean_obj_tag(x_776) == 0)
{
lean_dec_ref(x_776);
x_757 = lean_box(0);
goto block_775;
}
else
{
lean_object* x_777; lean_object* x_778; uint8_t x_779; uint8_t x_784; 
lean_dec_ref(x_756);
lean_dec(x_3);
x_777 = lean_ctor_get(x_776, 0);
x_784 = !lean_is_exclusive(x_776);
if (x_784 == 0)
{
x_778 = x_776;
x_779 = x_784;
goto block_783;
}
else
{
lean_inc(x_777);
lean_dec(x_776);
x_778 = lean_box(0);
x_779 = x_784;
goto block_783;
}
block_783:
{
lean_object* x_780; 
if (x_779 == 0)
{
x_780 = x_778;
goto block_781;
}
else
{
lean_object* x_782; 
x_782 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_782, 0, x_777);
x_780 = x_782;
goto block_781;
}
block_781:
{
return x_780;
}
}
}
}
block_797:
{
uint8_t x_788; 
x_788 = lean_nat_dec_lt(x_647, x_786);
if (x_788 == 0)
{
lean_dec_ref(x_755);
lean_dec(x_6);
x_757 = lean_box(0);
goto block_775;
}
else
{
lean_object* x_789; uint8_t x_790; 
x_789 = lean_box(0);
x_790 = lean_nat_dec_le(x_786, x_786);
if (x_790 == 0)
{
if (x_788 == 0)
{
lean_dec_ref(x_755);
lean_dec(x_6);
x_757 = lean_box(0);
goto block_775;
}
else
{
size_t x_791; size_t x_792; lean_object* x_793; 
x_791 = 0;
x_792 = lean_usize_of_nat(x_786);
x_793 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_755, x_791, x_792, x_789, x_6);
lean_dec(x_6);
lean_dec_ref(x_755);
x_776 = x_793;
goto block_785;
}
}
else
{
size_t x_794; size_t x_795; lean_object* x_796; 
x_794 = 0;
x_795 = lean_usize_of_nat(x_786);
x_796 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_755, x_794, x_795, x_789, x_6);
lean_dec(x_6);
lean_dec_ref(x_755);
x_776 = x_796;
goto block_785;
}
}
}
block_800:
{
if (x_798 == 0)
{
lean_inc_ref(x_756);
lean_inc_ref(x_755);
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_del_object(x_650);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec_ref(x_5);
x_787 = lean_box(0);
goto block_797;
}
else
{
if (x_147 == 0)
{
x_725 = x_3;
x_726 = x_5;
x_727 = x_6;
x_728 = x_229;
x_729 = x_8;
x_730 = lean_box(0);
goto block_751;
}
else
{
lean_inc_ref(x_756);
lean_inc_ref(x_755);
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_del_object(x_650);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec_ref(x_5);
x_787 = lean_box(0);
goto block_797;
}
}
}
}
else
{
lean_object* x_815; lean_object* x_816; 
lean_inc_ref(x_754);
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_del_object(x_650);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_815 = lean_ctor_get(x_754, 0);
lean_inc_ref(x_815);
lean_dec_ref(x_754);
if (x_628 == 0)
{
lean_ctor_set(x_627, 0, x_815);
x_816 = x_627;
goto block_817;
}
else
{
lean_object* x_818; 
x_818 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_818, 0, x_815);
x_816 = x_818;
goto block_817;
}
block_817:
{
return x_816;
}
}
}
block_680:
{
lean_object* x_660; 
x_660 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_658);
lean_dec(x_658);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; uint8_t x_662; uint8_t x_670; 
x_670 = !lean_is_exclusive(x_660);
if (x_670 == 0)
{
lean_object* x_671; 
x_671 = lean_ctor_get(x_660, 0);
lean_dec(x_671);
x_661 = x_660;
x_662 = x_670;
goto block_669;
}
else
{
lean_dec(x_660);
x_661 = lean_box(0);
x_662 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_663; 
if (x_645 == 0)
{
lean_ctor_set_tag(x_644, 6);
lean_ctor_set(x_644, 0, x_657);
x_663 = x_644;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_668, 0, x_657);
x_663 = x_668;
goto block_667;
}
block_667:
{
lean_object* x_664; 
if (x_662 == 0)
{
lean_ctor_set(x_661, 0, x_663);
x_664 = x_661;
goto block_665;
}
else
{
lean_object* x_666; 
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_663);
x_664 = x_666;
goto block_665;
}
block_665:
{
return x_664;
}
}
}
}
else
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; uint8_t x_679; 
lean_dec_ref(x_657);
lean_del_object(x_644);
x_672 = lean_ctor_get(x_660, 0);
x_679 = !lean_is_exclusive(x_660);
if (x_679 == 0)
{
x_673 = x_660;
x_674 = x_679;
goto block_678;
}
else
{
lean_inc(x_672);
lean_dec(x_660);
x_673 = lean_box(0);
x_674 = x_679;
goto block_678;
}
block_678:
{
lean_object* x_675; 
if (x_674 == 0)
{
x_675 = x_673;
goto block_676;
}
else
{
lean_object* x_677; 
x_677 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_677, 0, x_672);
x_675 = x_677;
goto block_676;
}
block_676:
{
return x_675;
}
}
}
}
block_691:
{
if (lean_obj_tag(x_682) == 0)
{
lean_dec_ref(x_682);
x_658 = x_681;
x_659 = lean_box(0);
goto block_680;
}
else
{
lean_object* x_683; lean_object* x_684; uint8_t x_685; uint8_t x_690; 
lean_dec(x_681);
lean_dec_ref(x_657);
lean_del_object(x_644);
x_683 = lean_ctor_get(x_682, 0);
x_690 = !lean_is_exclusive(x_682);
if (x_690 == 0)
{
x_684 = x_682;
x_685 = x_690;
goto block_689;
}
else
{
lean_inc(x_683);
lean_dec(x_682);
x_684 = lean_box(0);
x_685 = x_690;
goto block_689;
}
block_689:
{
lean_object* x_686; 
if (x_685 == 0)
{
x_686 = x_684;
goto block_687;
}
else
{
lean_object* x_688; 
x_688 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_688, 0, x_683);
x_686 = x_688;
goto block_687;
}
block_687:
{
return x_686;
}
}
}
}
block_708:
{
uint8_t x_699; 
x_699 = lean_nat_dec_lt(x_647, x_698);
if (x_699 == 0)
{
lean_dec(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec_ref(x_695);
lean_dec(x_694);
lean_dec(x_653);
x_658 = x_693;
x_659 = lean_box(0);
goto block_680;
}
else
{
lean_object* x_700; uint8_t x_701; 
x_700 = lean_box(0);
x_701 = lean_nat_dec_le(x_698, x_698);
if (x_701 == 0)
{
if (x_699 == 0)
{
lean_dec(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec_ref(x_695);
lean_dec(x_694);
lean_dec(x_653);
x_658 = x_693;
x_659 = lean_box(0);
goto block_680;
}
else
{
size_t x_702; size_t x_703; lean_object* x_704; 
x_702 = 0;
x_703 = lean_usize_of_nat(x_698);
lean_dec(x_698);
x_704 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_653, x_702, x_703, x_700, x_695, x_697, x_696, x_694);
lean_dec(x_694);
lean_dec_ref(x_696);
lean_dec(x_697);
lean_dec_ref(x_695);
lean_dec(x_653);
x_681 = x_693;
x_682 = x_704;
goto block_691;
}
}
else
{
size_t x_705; size_t x_706; lean_object* x_707; 
x_705 = 0;
x_706 = lean_usize_of_nat(x_698);
lean_dec(x_698);
x_707 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_653, x_705, x_706, x_700, x_695, x_697, x_696, x_694);
lean_dec(x_694);
lean_dec_ref(x_696);
lean_dec(x_697);
lean_dec_ref(x_695);
lean_dec(x_653);
x_681 = x_693;
x_682 = x_707;
goto block_691;
}
}
}
block_717:
{
lean_object* x_710; 
if (x_638 == 0)
{
lean_ctor_set(x_637, 3, x_653);
lean_ctor_set(x_637, 2, x_643);
lean_ctor_set(x_637, 1, x_657);
x_710 = x_637;
goto block_715;
}
else
{
lean_object* x_716; 
x_716 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_716, 0, x_633);
lean_ctor_set(x_716, 1, x_657);
lean_ctor_set(x_716, 2, x_643);
lean_ctor_set(x_716, 3, x_653);
x_710 = x_716;
goto block_715;
}
block_715:
{
lean_object* x_711; lean_object* x_712; 
x_711 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_711, 0, x_710);
if (x_655 == 0)
{
lean_ctor_set(x_654, 0, x_711);
x_712 = x_654;
goto block_713;
}
else
{
lean_object* x_714; 
x_714 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_714, 0, x_711);
x_712 = x_714;
goto block_713;
}
block_713:
{
return x_712;
}
}
}
block_724:
{
if (x_719 == 0)
{
lean_del_object(x_650);
lean_dec(x_635);
lean_dec_ref(x_1);
x_709 = lean_box(0);
goto block_717;
}
else
{
uint8_t x_720; 
x_720 = l_Lean_instBEqFVarId_beq(x_635, x_643);
lean_dec(x_635);
if (x_720 == 0)
{
lean_del_object(x_650);
lean_dec_ref(x_1);
x_709 = lean_box(0);
goto block_717;
}
else
{
lean_object* x_721; 
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec(x_633);
if (x_651 == 0)
{
lean_ctor_set(x_650, 0, x_1);
x_721 = x_650;
goto block_722;
}
else
{
lean_object* x_723; 
x_723 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_723, 0, x_1);
x_721 = x_723;
goto block_722;
}
block_722:
{
return x_721;
}
}
}
}
block_751:
{
lean_object* x_731; uint8_t x_732; 
x_731 = lean_array_get_size(x_653);
x_732 = lean_nat_dec_lt(x_647, x_731);
if (x_732 == 0)
{
lean_del_object(x_654);
lean_del_object(x_650);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec(x_135);
lean_dec(x_134);
x_692 = lean_box(0);
x_693 = x_725;
x_694 = x_729;
x_695 = x_726;
x_696 = x_728;
x_697 = x_727;
x_698 = x_731;
goto block_708;
}
else
{
if (x_732 == 0)
{
lean_del_object(x_654);
lean_del_object(x_650);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
lean_dec(x_135);
lean_dec(x_134);
x_692 = lean_box(0);
x_693 = x_725;
x_694 = x_729;
x_695 = x_726;
x_696 = x_728;
x_697 = x_727;
x_698 = x_731;
goto block_708;
}
else
{
size_t x_733; size_t x_734; uint8_t x_735; 
x_733 = 0;
x_734 = lean_usize_of_nat(x_731);
x_735 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_134, x_135, x_653, x_733, x_734);
lean_dec(x_135);
lean_dec(x_134);
if (x_735 == 0)
{
lean_del_object(x_654);
lean_del_object(x_650);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
x_692 = lean_box(0);
x_693 = x_725;
x_694 = x_729;
x_695 = x_726;
x_696 = x_728;
x_697 = x_727;
x_698 = x_731;
goto block_708;
}
else
{
if (x_147 == 0)
{
lean_object* x_736; 
lean_dec(x_729);
lean_dec_ref(x_728);
lean_dec(x_727);
lean_dec_ref(x_726);
lean_del_object(x_644);
lean_inc(x_643);
x_736 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_643, x_725);
lean_dec(x_725);
if (lean_obj_tag(x_736) == 0)
{
size_t x_737; size_t x_738; uint8_t x_739; 
lean_dec_ref(x_736);
x_737 = lean_ptr_addr(x_636);
lean_dec_ref(x_636);
x_738 = lean_ptr_addr(x_653);
x_739 = lean_usize_dec_eq(x_737, x_738);
if (x_739 == 0)
{
lean_dec_ref(x_634);
x_718 = lean_box(0);
x_719 = x_739;
goto block_724;
}
else
{
size_t x_740; size_t x_741; uint8_t x_742; 
x_740 = lean_ptr_addr(x_634);
lean_dec_ref(x_634);
x_741 = lean_ptr_addr(x_657);
x_742 = lean_usize_dec_eq(x_740, x_741);
x_718 = lean_box(0);
x_719 = x_742;
goto block_724;
}
}
else
{
lean_object* x_743; lean_object* x_744; uint8_t x_745; uint8_t x_750; 
lean_dec_ref(x_657);
lean_del_object(x_654);
lean_dec(x_653);
lean_del_object(x_650);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
x_743 = lean_ctor_get(x_736, 0);
x_750 = !lean_is_exclusive(x_736);
if (x_750 == 0)
{
x_744 = x_736;
x_745 = x_750;
goto block_749;
}
else
{
lean_inc(x_743);
lean_dec(x_736);
x_744 = lean_box(0);
x_745 = x_750;
goto block_749;
}
block_749:
{
lean_object* x_746; 
if (x_745 == 0)
{
x_746 = x_744;
goto block_747;
}
else
{
lean_object* x_748; 
x_748 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_748, 0, x_743);
x_746 = x_748;
goto block_747;
}
block_747:
{
return x_746;
}
}
}
}
else
{
lean_del_object(x_654);
lean_del_object(x_650);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec_ref(x_1);
x_692 = lean_box(0);
x_693 = x_725;
x_694 = x_729;
x_695 = x_726;
x_696 = x_728;
x_697 = x_727;
x_698 = x_731;
goto block_708;
}
}
}
}
}
}
}
else
{
lean_object* x_821; lean_object* x_822; uint8_t x_823; uint8_t x_828; 
lean_del_object(x_650);
lean_dec(x_646);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_del_object(x_627);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_821 = lean_ctor_get(x_652, 0);
x_828 = !lean_is_exclusive(x_652);
if (x_828 == 0)
{
x_822 = x_652;
x_823 = x_828;
goto block_827;
}
else
{
lean_inc(x_821);
lean_dec(x_652);
x_822 = lean_box(0);
x_823 = x_828;
goto block_827;
}
block_827:
{
lean_object* x_824; 
if (x_823 == 0)
{
x_824 = x_822;
goto block_825;
}
else
{
lean_object* x_826; 
x_826 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_826, 0, x_821);
x_824 = x_826;
goto block_825;
}
block_825:
{
return x_824;
}
}
}
}
}
else
{
lean_object* x_831; lean_object* x_832; uint8_t x_833; uint8_t x_838; 
lean_dec(x_646);
lean_del_object(x_644);
lean_dec(x_643);
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_del_object(x_627);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_831 = lean_ctor_get(x_648, 0);
x_838 = !lean_is_exclusive(x_648);
if (x_838 == 0)
{
x_832 = x_648;
x_833 = x_838;
goto block_837;
}
else
{
lean_inc(x_831);
lean_dec(x_648);
x_832 = lean_box(0);
x_833 = x_838;
goto block_837;
}
block_837:
{
lean_object* x_834; 
if (x_833 == 0)
{
x_834 = x_832;
goto block_835;
}
else
{
lean_object* x_836; 
x_836 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_836, 0, x_831);
x_834 = x_836;
goto block_835;
}
block_835:
{
return x_834;
}
}
}
}
}
else
{
lean_object* x_841; 
lean_del_object(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_del_object(x_627);
lean_dec_ref(x_1);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_841 = l_Lean_Compiler_LCNF_mkReturnErased(x_641, x_5, x_6, x_229, x_8);
lean_dec(x_8);
lean_dec_ref(x_229);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_841;
}
}
}
}
}
else
{
lean_object* x_846; lean_object* x_847; uint8_t x_848; uint8_t x_853; 
lean_dec_ref(x_624);
lean_dec_ref(x_1);
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_846 = lean_ctor_get(x_625, 0);
x_853 = !lean_is_exclusive(x_625);
if (x_853 == 0)
{
x_847 = x_625;
x_848 = x_853;
goto block_852;
}
else
{
lean_inc(x_846);
lean_dec(x_625);
x_847 = lean_box(0);
x_848 = x_853;
goto block_852;
}
block_852:
{
lean_object* x_849; 
if (x_848 == 0)
{
x_849 = x_847;
goto block_850;
}
else
{
lean_object* x_851; 
x_851 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_851, 0, x_846);
x_849 = x_851;
goto block_850;
}
block_850:
{
return x_849;
}
}
}
}
case 5:
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
lean_del_object(x_151);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_854 = lean_ctor_get(x_1, 0);
x_855 = lean_st_ref_get(x_3);
x_856 = lean_ctor_get(x_855, 0);
lean_inc_ref(x_856);
lean_dec(x_855);
lean_inc(x_854);
x_857 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_856, x_854, x_147);
lean_dec_ref(x_856);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; 
lean_dec_ref(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
lean_dec_ref(x_857);
lean_inc(x_858);
x_859 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_858, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; uint8_t x_861; uint8_t x_878; 
x_878 = !lean_is_exclusive(x_859);
if (x_878 == 0)
{
lean_object* x_879; 
x_879 = lean_ctor_get(x_859, 0);
lean_dec(x_879);
x_860 = x_859;
x_861 = x_878;
goto block_877;
}
else
{
lean_dec(x_859);
x_860 = lean_box(0);
x_861 = x_878;
goto block_877;
}
block_877:
{
uint8_t x_862; 
x_862 = l_Lean_instBEqFVarId_beq(x_854, x_858);
if (x_862 == 0)
{
lean_object* x_863; uint8_t x_864; uint8_t x_872; 
x_872 = !lean_is_exclusive(x_1);
if (x_872 == 0)
{
lean_object* x_873; 
x_873 = lean_ctor_get(x_1, 0);
lean_dec(x_873);
x_863 = x_1;
x_864 = x_872;
goto block_871;
}
else
{
lean_dec(x_1);
x_863 = lean_box(0);
x_864 = x_872;
goto block_871;
}
block_871:
{
lean_object* x_865; 
if (x_864 == 0)
{
lean_ctor_set(x_863, 0, x_858);
x_865 = x_863;
goto block_869;
}
else
{
lean_object* x_870; 
x_870 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_870, 0, x_858);
x_865 = x_870;
goto block_869;
}
block_869:
{
lean_object* x_866; 
if (x_861 == 0)
{
lean_ctor_set(x_860, 0, x_865);
x_866 = x_860;
goto block_867;
}
else
{
lean_object* x_868; 
x_868 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_868, 0, x_865);
x_866 = x_868;
goto block_867;
}
block_867:
{
return x_866;
}
}
}
}
else
{
lean_object* x_874; 
lean_dec(x_858);
if (x_861 == 0)
{
lean_ctor_set(x_860, 0, x_1);
x_874 = x_860;
goto block_875;
}
else
{
lean_object* x_876; 
x_876 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_876, 0, x_1);
x_874 = x_876;
goto block_875;
}
block_875:
{
return x_874;
}
}
}
}
else
{
lean_object* x_880; lean_object* x_881; uint8_t x_882; uint8_t x_887; 
lean_dec(x_858);
lean_dec_ref(x_1);
x_880 = lean_ctor_get(x_859, 0);
x_887 = !lean_is_exclusive(x_859);
if (x_887 == 0)
{
x_881 = x_859;
x_882 = x_887;
goto block_886;
}
else
{
lean_inc(x_880);
lean_dec(x_859);
x_881 = lean_box(0);
x_882 = x_887;
goto block_886;
}
block_886:
{
lean_object* x_883; 
if (x_882 == 0)
{
x_883 = x_881;
goto block_884;
}
else
{
lean_object* x_885; 
x_885 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_885, 0, x_880);
x_883 = x_885;
goto block_884;
}
block_884:
{
return x_883;
}
}
}
}
else
{
uint8_t x_888; lean_object* x_889; 
lean_dec_ref(x_1);
lean_dec(x_3);
x_888 = 0;
x_889 = l_Lean_Compiler_LCNF_mkReturnErased(x_888, x_5, x_6, x_229, x_8);
lean_dec(x_8);
lean_dec_ref(x_229);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_889;
}
}
case 6:
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; lean_object* x_894; size_t x_895; size_t x_896; uint8_t x_897; 
lean_dec_ref(x_229);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_890 = lean_ctor_get(x_1, 0);
x_891 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_892 = lean_ctor_get(x_891, 0);
lean_inc_ref(x_892);
lean_dec(x_891);
x_893 = 0;
lean_inc_ref(x_890);
x_894 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_893, x_892, x_147, x_890);
lean_dec_ref(x_892);
x_895 = lean_ptr_addr(x_890);
x_896 = lean_ptr_addr(x_894);
x_897 = lean_usize_dec_eq(x_895, x_896);
if (x_897 == 0)
{
lean_object* x_898; uint8_t x_899; uint8_t x_907; 
x_907 = !lean_is_exclusive(x_1);
if (x_907 == 0)
{
lean_object* x_908; 
x_908 = lean_ctor_get(x_1, 0);
lean_dec(x_908);
x_898 = x_1;
x_899 = x_907;
goto block_906;
}
else
{
lean_dec(x_1);
x_898 = lean_box(0);
x_899 = x_907;
goto block_906;
}
block_906:
{
lean_object* x_900; 
if (x_899 == 0)
{
lean_ctor_set(x_898, 0, x_894);
x_900 = x_898;
goto block_904;
}
else
{
lean_object* x_905; 
x_905 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_905, 0, x_894);
x_900 = x_905;
goto block_904;
}
block_904:
{
lean_object* x_901; 
if (x_152 == 0)
{
lean_ctor_set(x_151, 0, x_900);
x_901 = x_151;
goto block_902;
}
else
{
lean_object* x_903; 
x_903 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_903, 0, x_900);
x_901 = x_903;
goto block_902;
}
block_902:
{
return x_901;
}
}
}
}
else
{
lean_object* x_909; 
lean_dec_ref(x_894);
if (x_152 == 0)
{
lean_ctor_set(x_151, 0, x_1);
x_909 = x_151;
goto block_910;
}
else
{
lean_object* x_911; 
x_911 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_911, 0, x_1);
x_909 = x_911;
goto block_910;
}
block_910:
{
return x_909;
}
}
}
default: 
{
lean_object* x_912; lean_object* x_913; 
lean_del_object(x_151);
lean_dec(x_135);
lean_dec(x_134);
x_912 = lean_ctor_get(x_1, 0);
x_913 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_913);
lean_inc_ref(x_912);
x_153 = x_912;
x_154 = x_913;
x_155 = x_2;
x_156 = x_3;
x_157 = x_4;
x_158 = x_5;
x_159 = x_6;
x_160 = x_229;
x_161 = x_8;
goto block_226;
}
}
}
}
}
else
{
lean_object* x_919; lean_object* x_920; uint8_t x_921; uint8_t x_926; 
lean_del_object(x_148);
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_919 = lean_ctor_get(x_150, 0);
x_926 = !lean_is_exclusive(x_150);
if (x_926 == 0)
{
x_920 = x_150;
x_921 = x_926;
goto block_925;
}
else
{
lean_inc(x_919);
lean_dec(x_150);
x_920 = lean_box(0);
x_921 = x_926;
goto block_925;
}
block_925:
{
lean_object* x_922; 
if (x_921 == 0)
{
x_922 = x_920;
goto block_923;
}
else
{
lean_object* x_924; 
x_924 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_924, 0, x_919);
x_922 = x_924;
goto block_923;
}
block_923:
{
return x_922;
}
}
}
}
}
else
{
lean_object* x_943; 
lean_dec_ref(x_1);
x_943 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_943;
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_12);
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
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_20);
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
x_19 = lean_box(0);
x_20 = x_27;
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
x_19 = lean_box(0);
x_20 = x_27;
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
x_11 = lean_box(0);
x_12 = x_27;
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
x_11 = lean_box(0);
x_12 = x_27;
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
x_45 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
x_46 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
block_100:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
x_60 = l_Lean_Compiler_LCNF_Simp_simp(x_50, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
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
lean_object* x_67; uint8_t x_68; uint8_t x_73; 
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_66, 0);
lean_dec(x_74);
x_67 = x_66;
x_68 = x_73;
goto block_72;
}
else
{
lean_dec(x_66);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_61);
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_61);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_61);
x_75 = lean_ctor_get(x_66, 0);
x_82 = !lean_is_exclusive(x_66);
if (x_82 == 0)
{
x_76 = x_66;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_66);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
else
{
if (x_49 == 0)
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
lean_object* x_83; 
lean_inc_ref(x_51);
x_83 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_26 = x_51;
x_27 = x_61;
x_28 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_61);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_83, 0);
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
x_85 = x_83;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
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
x_92 = lean_ctor_get(x_63, 0);
x_99 = !lean_is_exclusive(x_63);
if (x_99 == 0)
{
x_93 = x_63;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_63);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
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
block_122:
{
lean_object* x_112; 
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc_ref(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
x_112 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_49 = x_101;
x_50 = x_102;
x_51 = x_113;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_107;
x_56 = x_108;
x_57 = x_109;
x_58 = x_110;
x_59 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_112, 0);
x_121 = !lean_is_exclusive(x_112);
if (x_121 == 0)
{
x_115 = x_112;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
block_130:
{
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_1);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec_ref(x_125);
lean_dec_ref(x_123);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_1);
return x_129;
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
x_18 = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(x_15, x_16, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_24 = x_20;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_1, x_2, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_1, x_2, x_3, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_1, x_2, x_3, x_4, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(x_1, x_2, x_3, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(x_1, x_2, x_3, x_4, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_2);
x_15 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(x_2, x_3, x_4, x_5);
return x_6;
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
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin)
;
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
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_Main(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
}
#ifdef __cplusplus
}
#endif
