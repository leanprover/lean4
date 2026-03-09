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
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_36 = l_Lean_Compiler_LCNF_Code_internalize(x_34, x_11, x_33, x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_37);
x_38 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_37, x_35, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_38);
x_39 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
x_40 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_32, x_37, x_39, x_5, x_6, x_7, x_8);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_37);
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
x_49 = lean_ctor_get(x_36, 0);
x_56 = !lean_is_exclusive(x_36);
if (x_56 == 0)
{
x_50 = x_36;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_36);
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
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
goto block_5;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
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
lean_object* x_10; lean_object* x_15; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uget_borrowed(x_1, x_2);
x_21 = l_Lean_Compiler_LCNF_Alt_getParams(x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_19, x_22);
if (x_24 == 0)
{
lean_dec_ref(x_21);
x_10 = x_23;
goto block_14;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec_ref(x_21);
x_10 = x_23;
goto block_14;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_22);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_21, x_26, x_27, x_23, x_6);
lean_dec_ref(x_21);
x_15 = x_28;
goto block_17;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(x_21, x_29, x_30, x_23, x_6);
lean_dec_ref(x_21);
x_15 = x_31;
goto block_17;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
block_17:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_10 = x_16;
goto block_14;
}
else
{
return x_15;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_342; 
x_14 = lean_ctor_get(x_13, 0);
x_342 = !lean_is_exclusive(x_13);
if (x_342 == 0)
{
x_15 = x_13;
x_16 = x_342;
goto block_341;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_342;
goto block_341;
}
block_341:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_336; 
lean_del_object(x_15);
x_17 = lean_ctor_get(x_14, 0);
x_336 = !lean_is_exclusive(x_14);
if (x_336 == 0)
{
x_18 = x_14;
x_19 = x_336;
goto block_335;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
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
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_12, 0);
lean_inc(x_311);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
lean_inc(x_311);
x_312 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(x_24, x_311, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_326; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec_ref(x_312);
x_314 = lean_ctor_get(x_3, 0);
x_315 = lean_ctor_get(x_3, 1);
x_316 = lean_ctor_get(x_3, 2);
x_317 = lean_ctor_get(x_3, 3);
x_326 = !lean_is_exclusive(x_3);
if (x_326 == 0)
{
x_318 = x_3;
x_319 = x_326;
goto block_325;
}
else
{
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_3);
x_318 = lean_box(0);
x_319 = x_326;
goto block_325;
}
block_325:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_inc(x_311);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_311);
lean_ctor_set(x_320, 1, x_316);
x_321 = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(x_317, x_311, x_313);
if (x_319 == 0)
{
lean_ctor_set(x_318, 3, x_321);
lean_ctor_set(x_318, 2, x_320);
x_322 = x_318;
goto block_323;
}
else
{
lean_object* x_324; 
x_324 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_320);
lean_ctor_set(x_324, 3, x_321);
x_322 = x_324;
goto block_323;
}
block_323:
{
x_209 = x_322;
x_210 = x_4;
x_211 = x_5;
x_212 = x_6;
x_213 = x_7;
x_214 = x_8;
x_215 = x_9;
goto block_310;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_334; 
lean_dec(x_311);
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
x_327 = lean_ctor_get(x_312, 0);
x_334 = !lean_is_exclusive(x_312);
if (x_334 == 0)
{
x_328 = x_312;
x_329 = x_334;
goto block_333;
}
else
{
lean_inc(x_327);
lean_dec(x_312);
x_328 = lean_box(0);
x_329 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_330; 
if (x_329 == 0)
{
x_330 = x_328;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_327);
x_330 = x_332;
goto block_331;
}
block_331:
{
return x_330;
}
}
}
}
else
{
lean_dec(x_12);
x_209 = x_3;
x_210 = x_4;
x_211 = x_5;
x_212 = x_6;
x_213 = x_7;
x_214 = x_8;
x_215 = x_9;
goto block_310;
}
block_208:
{
lean_object* x_41; 
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
lean_inc_ref(x_34);
lean_inc(x_35);
lean_inc_ref(x_31);
x_41 = l_Lean_Compiler_LCNF_Simp_simp(x_37, x_31, x_35, x_34, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_35);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec_ref(x_43);
lean_inc(x_42);
x_44 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_38);
x_45 = lean_mk_empty_array_with_capacity(x_36);
lean_dec(x_36);
lean_inc_ref(x_45);
x_46 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(x_39, x_45);
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
x_47 = l_Lean_Compiler_LCNF_inferAppType(x_32, x_22, x_46, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_48);
x_49 = l_Lean_Expr_headBeta(x_48);
x_50 = l_Lean_Expr_isForall(x_49);
lean_dec_ref(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_45);
x_51 = l_Lean_Compiler_LCNF_mkAuxParam(x_32, x_48, x_27, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
lean_inc(x_53);
x_54 = lean_apply_9(x_30, x_53, x_31, x_35, x_34, x_40, x_28, x_29, x_33, lean_box(0));
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_array_push(x_57, x_52);
x_59 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1));
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
x_60 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_32, x_58, x_55, x_59, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc(x_61);
x_62 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed), 8, 2);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_56);
x_63 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_32, x_42, x_62, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_75; 
x_64 = lean_ctor_get(x_63, 0);
x_75 = !lean_is_exclusive(x_63);
if (x_75 == 0)
{
x_65 = x_63;
x_66 = x_75;
goto block_74;
}
else
{
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_64);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_67);
x_68 = x_18;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_67);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_68);
x_69 = x_65;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_61);
lean_del_object(x_18);
x_76 = lean_ctor_get(x_63, 0);
x_83 = !lean_is_exclusive(x_63);
if (x_83 == 0)
{
x_77 = x_63;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_63);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_84 = lean_ctor_get(x_60, 0);
x_91 = !lean_is_exclusive(x_60);
if (x_91 == 0)
{
x_85 = x_60;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_60);
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
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_52);
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_92 = lean_ctor_get(x_54, 0);
x_99 = !lean_is_exclusive(x_54);
if (x_99 == 0)
{
x_93 = x_54;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_54);
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
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_100 = lean_ctor_get(x_51, 0);
x_107 = !lean_is_exclusive(x_51);
if (x_107 == 0)
{
x_101 = x_51;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_51);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_48);
x_108 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4));
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
x_109 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_45, x_42, x_108, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
x_111 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_110, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_33);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_40);
lean_inc_ref(x_34);
lean_inc(x_35);
lean_inc_ref(x_31);
lean_inc(x_113);
x_114 = lean_apply_9(x_30, x_113, x_31, x_35, x_34, x_40, x_28, x_29, x_33, lean_box(0));
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_112);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_mk_empty_array_with_capacity(x_117);
x_119 = lean_array_push(x_118, x_116);
x_120 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_119, x_115, x_31, x_35, x_34, x_40, x_28, x_29, x_33);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_40);
lean_dec_ref(x_34);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_131; 
x_121 = lean_ctor_get(x_120, 0);
x_131 = !lean_is_exclusive(x_120);
if (x_131 == 0)
{
x_122 = x_120;
x_123 = x_131;
goto block_130;
}
else
{
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_124; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_121);
x_124 = x_18;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_121);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_124);
x_125 = x_122;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_124);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_139; 
lean_del_object(x_18);
x_132 = lean_ctor_get(x_120, 0);
x_139 = !lean_is_exclusive(x_120);
if (x_139 == 0)
{
x_133 = x_120;
x_134 = x_139;
goto block_138;
}
else
{
lean_inc(x_132);
lean_dec(x_120);
x_133 = lean_box(0);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_134 == 0)
{
x_135 = x_133;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_112);
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_140 = lean_ctor_get(x_114, 0);
x_147 = !lean_is_exclusive(x_114);
if (x_147 == 0)
{
x_141 = x_114;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_114);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_148 = lean_ctor_get(x_111, 0);
x_155 = !lean_is_exclusive(x_111);
if (x_155 == 0)
{
x_149 = x_111;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_111);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_156 = lean_ctor_get(x_109, 0);
x_163 = !lean_is_exclusive(x_109);
if (x_163 == 0)
{
x_157 = x_109;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_109);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec_ref(x_45);
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_del_object(x_18);
x_164 = lean_ctor_get(x_47, 0);
x_171 = !lean_is_exclusive(x_47);
if (x_171 == 0)
{
x_165 = x_47;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_47);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
else
{
lean_object* x_172; 
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_22);
x_172 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_32, x_42, x_38, x_40, x_28, x_29, x_33);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_183; 
x_173 = lean_ctor_get(x_172, 0);
x_183 = !lean_is_exclusive(x_172);
if (x_183 == 0)
{
x_174 = x_172;
x_175 = x_183;
goto block_182;
}
else
{
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_box(0);
x_175 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_176; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_173);
x_176 = x_18;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_173);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_175 == 0)
{
lean_ctor_set(x_174, 0, x_176);
x_177 = x_174;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_176);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
lean_del_object(x_18);
x_184 = lean_ctor_get(x_172, 0);
x_191 = !lean_is_exclusive(x_172);
if (x_191 == 0)
{
x_185 = x_172;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_dec(x_172);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_199; 
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_192 = lean_ctor_get(x_43, 0);
x_199 = !lean_is_exclusive(x_43);
if (x_199 == 0)
{
x_193 = x_43;
x_194 = x_199;
goto block_198;
}
else
{
lean_inc(x_192);
lean_dec(x_43);
x_193 = lean_box(0);
x_194 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_195; 
if (x_194 == 0)
{
x_195 = x_193;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_192);
x_195 = x_197;
goto block_196;
}
block_196:
{
return x_195;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_200 = lean_ctor_get(x_41, 0);
x_207 = !lean_is_exclusive(x_41);
if (x_207 == 0)
{
x_201 = x_41;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_41);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
block_310:
{
if (x_27 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
lean_dec(x_17);
x_216 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
lean_inc_ref(x_23);
x_217 = l_Array_toSubarray___redArg(x_23, x_216, x_26);
lean_inc_ref(x_217);
x_218 = l_Subarray_copy___redArg(x_217);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc_ref(x_212);
x_219 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_20, x_21, x_218, x_27, x_209, x_210, x_211, x_212, x_213, x_214, x_215);
lean_dec_ref(x_20);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = 0;
x_222 = lean_box(x_221);
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc(x_26);
x_223 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 16, 7);
lean_closure_set(x_223, 0, x_26);
lean_closure_set(x_223, 1, x_25);
lean_closure_set(x_223, 2, x_11);
lean_closure_set(x_223, 3, x_2);
lean_closure_set(x_223, 4, x_23);
lean_closure_set(x_223, 5, x_222);
lean_closure_set(x_223, 6, x_216);
lean_inc_ref(x_211);
lean_inc_ref(x_209);
lean_inc_ref(x_223);
lean_inc(x_210);
x_224 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed), 10, 4);
lean_closure_set(x_224, 0, x_210);
lean_closure_set(x_224, 1, x_223);
lean_closure_set(x_224, 2, x_209);
lean_closure_set(x_224, 3, x_211);
x_225 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_2, x_11);
lean_dec(x_11);
lean_dec_ref(x_2);
if (x_225 == 0)
{
lean_dec(x_26);
x_28 = x_213;
x_29 = x_214;
x_30 = x_223;
x_31 = x_209;
x_32 = x_221;
x_33 = x_215;
x_34 = x_211;
x_35 = x_210;
x_36 = x_216;
x_37 = x_220;
x_38 = x_224;
x_39 = x_217;
x_40 = x_212;
goto block_208;
}
else
{
uint8_t x_226; 
x_226 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
if (x_226 == 0)
{
x_28 = x_213;
x_29 = x_214;
x_30 = x_223;
x_31 = x_209;
x_32 = x_221;
x_33 = x_215;
x_34 = x_211;
x_35 = x_210;
x_36 = x_216;
x_37 = x_220;
x_38 = x_224;
x_39 = x_217;
x_40 = x_212;
goto block_208;
}
else
{
lean_object* x_227; 
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_217);
lean_dec_ref(x_22);
lean_del_object(x_18);
x_227 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_210);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
lean_dec_ref(x_227);
x_228 = l_Lean_Compiler_LCNF_Simp_simp(x_220, x_209, x_210, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_237; 
x_229 = lean_ctor_get(x_228, 0);
x_237 = !lean_is_exclusive(x_228);
if (x_237 == 0)
{
x_230 = x_228;
x_231 = x_237;
goto block_236;
}
else
{
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_box(0);
x_231 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_229);
if (x_231 == 0)
{
lean_ctor_set(x_230, 0, x_232);
x_233 = x_230;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_232);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_245; 
x_238 = lean_ctor_get(x_228, 0);
x_245 = !lean_is_exclusive(x_228);
if (x_245 == 0)
{
x_239 = x_228;
x_240 = x_245;
goto block_244;
}
else
{
lean_inc(x_238);
lean_dec(x_228);
x_239 = lean_box(0);
x_240 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_241; 
if (x_240 == 0)
{
x_241 = x_239;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_238);
x_241 = x_243;
goto block_242;
}
block_242:
{
return x_241;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_253; 
lean_dec(x_220);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
x_246 = lean_ctor_get(x_227, 0);
x_253 = !lean_is_exclusive(x_227);
if (x_253 == 0)
{
x_247 = x_227;
x_248 = x_253;
goto block_252;
}
else
{
lean_inc(x_246);
lean_dec(x_227);
x_247 = lean_box(0);
x_248 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_249; 
if (x_248 == 0)
{
x_249 = x_247;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_246);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_261; 
lean_dec_ref(x_217);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_del_object(x_18);
lean_dec(x_11);
lean_dec_ref(x_2);
x_254 = lean_ctor_get(x_219, 0);
x_261 = !lean_is_exclusive(x_219);
if (x_261 == 0)
{
x_255 = x_219;
x_256 = x_261;
goto block_260;
}
else
{
lean_inc(x_254);
lean_dec(x_219);
x_255 = lean_box(0);
x_256 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_257; 
if (x_256 == 0)
{
x_257 = x_255;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_254);
x_257 = x_259;
goto block_258;
}
block_258:
{
return x_257;
}
}
}
}
else
{
lean_object* x_262; 
lean_dec(x_26);
lean_del_object(x_18);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc_ref(x_212);
x_262 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_17, x_209, x_210, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_11, x_264, x_210, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
lean_dec_ref(x_265);
x_266 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_210);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec_ref(x_266);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set(x_267, 1, x_2);
x_268 = l_Lean_Compiler_LCNF_Simp_simp(x_267, x_209, x_210, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_277; 
x_269 = lean_ctor_get(x_268, 0);
x_277 = !lean_is_exclusive(x_268);
if (x_277 == 0)
{
x_270 = x_268;
x_271 = x_277;
goto block_276;
}
else
{
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_box(0);
x_271 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_269);
if (x_271 == 0)
{
lean_ctor_set(x_270, 0, x_272);
x_273 = x_270;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_272);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_285; 
x_278 = lean_ctor_get(x_268, 0);
x_285 = !lean_is_exclusive(x_268);
if (x_285 == 0)
{
x_279 = x_268;
x_280 = x_285;
goto block_284;
}
else
{
lean_inc(x_278);
lean_dec(x_268);
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
lean_dec(x_263);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec_ref(x_2);
x_286 = lean_ctor_get(x_266, 0);
x_293 = !lean_is_exclusive(x_266);
if (x_293 == 0)
{
x_287 = x_266;
x_288 = x_293;
goto block_292;
}
else
{
lean_inc(x_286);
lean_dec(x_266);
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
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_301; 
lean_dec(x_263);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec_ref(x_2);
x_294 = lean_ctor_get(x_265, 0);
x_301 = !lean_is_exclusive(x_265);
if (x_301 == 0)
{
x_295 = x_265;
x_296 = x_301;
goto block_300;
}
else
{
lean_inc(x_294);
lean_dec(x_265);
x_295 = lean_box(0);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
if (x_296 == 0)
{
x_297 = x_295;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_294);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_309; 
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_11);
lean_dec_ref(x_2);
x_302 = lean_ctor_get(x_262, 0);
x_309 = !lean_is_exclusive(x_262);
if (x_309 == 0)
{
x_303 = x_262;
x_304 = x_309;
goto block_308;
}
else
{
lean_inc(x_302);
lean_dec(x_262);
x_303 = lean_box(0);
x_304 = x_309;
goto block_308;
}
block_308:
{
lean_object* x_305; 
if (x_304 == 0)
{
x_305 = x_303;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_302);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; 
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
x_337 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_337);
x_338 = x_15;
goto block_339;
}
else
{
lean_object* x_340; 
x_340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_340, 0, x_337);
x_338 = x_340;
goto block_339;
}
block_339:
{
return x_338;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; uint8_t x_350; 
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
x_343 = lean_ctor_get(x_13, 0);
x_350 = !lean_is_exclusive(x_13);
if (x_350 == 0)
{
x_344 = x_13;
x_345 = x_350;
goto block_349;
}
else
{
lean_inc(x_343);
lean_dec(x_13);
x_344 = lean_box(0);
x_345 = x_350;
goto block_349;
}
block_349:
{
lean_object* x_346; 
if (x_345 == 0)
{
x_346 = x_344;
goto block_347;
}
else
{
lean_object* x_348; 
x_348 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_348, 0, x_343);
x_346 = x_348;
goto block_347;
}
block_347:
{
return x_346;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_st_ref_get(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = 0;
lean_inc(x_14);
x_19 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_16, x_14, x_18);
lean_dec_ref(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_20, x_4, x_6, x_8);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_251; 
x_22 = lean_ctor_get(x_21, 0);
x_251 = !lean_is_exclusive(x_21);
if (x_251 == 0)
{
x_23 = x_21;
x_24 = x_251;
goto block_250;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_251;
goto block_250;
}
block_250:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_245; 
x_25 = lean_ctor_get(x_22, 0);
x_245 = !lean_is_exclusive(x_22);
if (x_245 == 0)
{
x_26 = x_22;
x_27 = x_245;
goto block_244;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_25);
lean_inc(x_30);
x_31 = l_Lean_Environment_find_x3f(x_29, x_30, x_18);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_243; 
x_32 = lean_ctor_get(x_31, 0);
x_243 = !lean_is_exclusive(x_31);
if (x_243 == 0)
{
x_33 = x_31;
x_34 = x_243;
goto block_242;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_243;
goto block_242;
}
block_242:
{
if (lean_obj_tag(x_32) == 6)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_241; 
x_35 = lean_ctor_get(x_32, 0);
x_241 = !lean_is_exclusive(x_32);
if (x_241 == 0)
{
x_36 = x_32;
x_37 = x_241;
goto block_240;
}
else
{
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec_ref(x_35);
x_39 = lean_name_eq(x_13, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_del_object(x_36);
lean_del_object(x_33);
lean_dec(x_30);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_40);
x_41 = x_23;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_239; 
lean_del_object(x_23);
x_44 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0, &l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0);
x_45 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_17, x_1, x_30);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
x_239 = !lean_is_exclusive(x_45);
if (x_239 == 0)
{
x_48 = x_45;
x_49 = x_239;
goto block_238;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_50; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 4);
lean_ctor_set(x_36, 0, x_47);
x_50 = x_36;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_237, 0, x_47);
x_50 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_51; 
x_51 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_17, x_50, x_6);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec_ref(x_51);
x_52 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
if (lean_obj_tag(x_46) == 0)
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_del_object(x_48);
lean_del_object(x_26);
x_53 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_46);
x_55 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_25);
x_102 = lean_ctor_get(x_55, 3);
lean_inc(x_102);
lean_dec_ref(x_55);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_array_get_size(x_56);
x_105 = lean_nat_dec_le(x_102, x_103);
if (x_105 == 0)
{
x_57 = x_102;
x_58 = x_104;
goto block_101;
}
else
{
lean_dec(x_102);
x_57 = x_103;
x_58 = x_104;
goto block_101;
}
block_101:
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = l_Array_toSubarray___redArg(x_56, x_57, x_58);
x_60 = lean_array_size(x_53);
x_61 = 0;
x_62 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(x_53, x_60, x_61, x_59, x_3);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec_ref(x_62);
lean_inc(x_6);
x_63 = l_Lean_Compiler_LCNF_Simp_simp(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_17, x_53, x_6);
lean_dec(x_6);
lean_dec_ref(x_53);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; uint8_t x_75; 
x_75 = !lean_is_exclusive(x_65);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_65, 0);
lean_dec(x_76);
x_66 = x_65;
x_67 = x_75;
goto block_74;
}
else
{
lean_dec(x_65);
x_66 = lean_box(0);
x_67 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_68; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_64);
x_68 = x_33;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_64);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_68);
x_69 = x_66;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_del_object(x_33);
x_77 = lean_ctor_get(x_65, 0);
x_84 = !lean_is_exclusive(x_65);
if (x_84 == 0)
{
x_78 = x_65;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_65);
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
lean_dec_ref(x_53);
lean_del_object(x_33);
lean_dec(x_6);
x_85 = lean_ctor_get(x_63, 0);
x_92 = !lean_is_exclusive(x_63);
if (x_92 == 0)
{
x_86 = x_63;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_63);
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
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_del_object(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_93 = lean_ctor_get(x_62, 0);
x_100 = !lean_is_exclusive(x_62);
if (x_100 == 0)
{
x_94 = x_62;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_62);
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
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_198; 
x_106 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_46, 2);
lean_inc_ref(x_107);
lean_dec_ref(x_46);
x_108 = lean_ctor_get(x_25, 0);
x_198 = !lean_is_exclusive(x_25);
if (x_198 == 0)
{
x_109 = x_25;
x_110 = x_198;
goto block_197;
}
else
{
lean_inc(x_108);
lean_dec(x_25);
x_109 = lean_box(0);
x_110 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_dec_eq(x_108, x_111);
if (x_112 == 1)
{
lean_object* x_113; 
lean_del_object(x_109);
lean_dec(x_108);
lean_dec_ref(x_106);
lean_del_object(x_48);
lean_del_object(x_26);
x_113 = l_Lean_Compiler_LCNF_Simp_simp(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_124; 
x_114 = lean_ctor_get(x_113, 0);
x_124 = !lean_is_exclusive(x_113);
if (x_124 == 0)
{
x_115 = x_113;
x_116 = x_124;
goto block_123;
}
else
{
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_box(0);
x_116 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_117; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_114);
x_117 = x_33;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_114);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_116 == 0)
{
lean_ctor_set(x_115, 0, x_117);
x_118 = x_115;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_117);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_del_object(x_33);
x_125 = lean_ctor_get(x_113, 0);
x_132 = !lean_is_exclusive(x_113);
if (x_132 == 0)
{
x_126 = x_113;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_113);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_sub(x_108, x_133);
lean_dec(x_108);
if (x_110 == 0)
{
lean_ctor_set_tag(x_109, 0);
lean_ctor_set(x_109, 0, x_134);
x_135 = x_109;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_134);
x_135 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_136; 
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_135);
x_136 = x_26;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_135);
x_136 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_137; lean_object* x_138; 
x_137 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_138 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_17, x_136, x_137, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_array_get_borrowed(x_44, x_106, x_111);
x_141 = lean_ctor_get(x_140, 0);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
lean_inc(x_141);
x_143 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_141, x_142, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec_ref(x_143);
lean_inc(x_6);
x_144 = l_Lean_Compiler_LCNF_Simp_simp(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_17, x_106, x_6);
lean_dec(x_6);
lean_dec_ref(x_106);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; uint8_t x_148; uint8_t x_159; 
x_159 = !lean_is_exclusive(x_146);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_146, 0);
lean_dec(x_160);
x_147 = x_146;
x_148 = x_159;
goto block_158;
}
else
{
lean_dec(x_146);
x_147 = lean_box(0);
x_148 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_149; 
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_145);
lean_ctor_set(x_48, 0, x_139);
x_149 = x_48;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_139);
lean_ctor_set(x_157, 1, x_145);
x_149 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_150; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_149);
x_150 = x_33;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_149);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_150);
x_151 = x_147;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_145);
lean_dec(x_139);
lean_del_object(x_48);
lean_del_object(x_33);
x_161 = lean_ctor_get(x_146, 0);
x_168 = !lean_is_exclusive(x_146);
if (x_168 == 0)
{
x_162 = x_146;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_146);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_176; 
lean_dec(x_139);
lean_dec_ref(x_106);
lean_del_object(x_48);
lean_del_object(x_33);
lean_dec(x_6);
x_169 = lean_ctor_get(x_144, 0);
x_176 = !lean_is_exclusive(x_144);
if (x_176 == 0)
{
x_170 = x_144;
x_171 = x_176;
goto block_175;
}
else
{
lean_inc(x_169);
lean_dec(x_144);
x_170 = lean_box(0);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; 
if (x_171 == 0)
{
x_172 = x_170;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_169);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_184; 
lean_dec(x_139);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_del_object(x_48);
lean_del_object(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_177 = lean_ctor_get(x_143, 0);
x_184 = !lean_is_exclusive(x_143);
if (x_184 == 0)
{
x_178 = x_143;
x_179 = x_184;
goto block_183;
}
else
{
lean_inc(x_177);
lean_dec(x_143);
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
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_del_object(x_48);
lean_del_object(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_185 = lean_ctor_get(x_138, 0);
x_192 = !lean_is_exclusive(x_138);
if (x_192 == 0)
{
x_186 = x_138;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_138);
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
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_del_object(x_48);
lean_del_object(x_26);
lean_dec(x_25);
x_199 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_199);
lean_dec_ref(x_46);
x_200 = l_Lean_Compiler_LCNF_Simp_simp(x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_211; 
x_201 = lean_ctor_get(x_200, 0);
x_211 = !lean_is_exclusive(x_200);
if (x_211 == 0)
{
x_202 = x_200;
x_203 = x_211;
goto block_210;
}
else
{
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_box(0);
x_203 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_204; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_201);
x_204 = x_33;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_201);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_203 == 0)
{
lean_ctor_set(x_202, 0, x_204);
x_205 = x_202;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_204);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_219; 
lean_del_object(x_33);
x_212 = lean_ctor_get(x_200, 0);
x_219 = !lean_is_exclusive(x_200);
if (x_219 == 0)
{
x_213 = x_200;
x_214 = x_219;
goto block_218;
}
else
{
lean_inc(x_212);
lean_dec(x_200);
x_213 = lean_box(0);
x_214 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_215; 
if (x_214 == 0)
{
x_215 = x_213;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_212);
x_215 = x_217;
goto block_216;
}
block_216:
{
return x_215;
}
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_227; 
lean_del_object(x_48);
lean_dec(x_46);
lean_del_object(x_33);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_220 = lean_ctor_get(x_52, 0);
x_227 = !lean_is_exclusive(x_52);
if (x_227 == 0)
{
x_221 = x_52;
x_222 = x_227;
goto block_226;
}
else
{
lean_inc(x_220);
lean_dec(x_52);
x_221 = lean_box(0);
x_222 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_223; 
if (x_222 == 0)
{
x_223 = x_221;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_220);
x_223 = x_225;
goto block_224;
}
block_224:
{
return x_223;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_235; 
lean_del_object(x_48);
lean_dec(x_46);
lean_del_object(x_33);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_51, 0);
x_235 = !lean_is_exclusive(x_51);
if (x_235 == 0)
{
x_229 = x_51;
x_230 = x_235;
goto block_234;
}
else
{
lean_inc(x_228);
lean_dec(x_51);
x_229 = lean_box(0);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_230 == 0)
{
x_231 = x_229;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_228);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
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
lean_del_object(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_12;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_12;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_246 = lean_box(0);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_246);
x_247 = x_23;
goto block_248;
}
else
{
lean_object* x_249; 
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_246);
x_247 = x_249;
goto block_248;
}
block_248:
{
return x_247;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_259; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_252 = lean_ctor_get(x_21, 0);
x_259 = !lean_is_exclusive(x_21);
if (x_259 == 0)
{
x_253 = x_21;
x_254 = x_259;
goto block_258;
}
else
{
lean_inc(x_252);
lean_dec(x_21);
x_253 = lean_box(0);
x_254 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_255; 
if (x_254 == 0)
{
x_255 = x_253;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_252);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
}
else
{
lean_object* x_260; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_260 = l_Lean_Compiler_LCNF_mkReturnErased(x_17, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_269; 
x_261 = lean_ctor_get(x_260, 0);
x_269 = !lean_is_exclusive(x_260);
if (x_269 == 0)
{
x_262 = x_260;
x_263 = x_269;
goto block_268;
}
else
{
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_box(0);
x_263 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_261);
if (x_263 == 0)
{
lean_ctor_set(x_262, 0, x_264);
x_265 = x_262;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_277; 
x_270 = lean_ctor_get(x_260, 0);
x_277 = !lean_is_exclusive(x_260);
if (x_277 == 0)
{
x_271 = x_260;
x_272 = x_277;
goto block_276;
}
else
{
lean_inc(x_270);
lean_dec(x_260);
x_271 = lean_box(0);
x_272 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_273; 
if (x_272 == 0)
{
x_273 = x_271;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_270);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget_borrowed(x_5, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_87; uint8_t x_88; uint8_t x_90; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
x_32 = lean_ctor_get(x_17, 2);
x_33 = 0;
x_87 = lean_nat_dec_eq(x_2, x_3);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_array_get_size(x_31);
x_94 = lean_nat_dec_lt(x_92, x_93);
if (x_94 == 0)
{
x_90 = x_87;
goto block_91;
}
else
{
if (x_94 == 0)
{
x_90 = x_87;
goto block_91;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_93);
x_97 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(x_31, x_95, x_96, x_12);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
x_90 = x_99;
goto block_91;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
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
x_100 = lean_ctor_get(x_97, 0);
x_107 = !lean_is_exclusive(x_97);
if (x_107 == 0)
{
x_101 = x_97;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
}
block_86:
{
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_35 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_32);
x_37 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_6, x_7, x_36, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_17);
x_39 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_38);
x_18 = x_39;
goto block_29;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
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
x_40 = lean_ctor_get(x_37, 0);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
x_41 = x_37;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
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
x_48 = lean_ctor_get(x_35, 0);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
x_49 = x_35;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_56; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_32);
x_56 = l_Lean_Compiler_LCNF_Code_inferType(x_33, x_32, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_33, x_32, x_10);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec_ref(x_58);
x_59 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_59);
x_60 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_60, 0, x_57);
lean_inc_ref(x_17);
x_61 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_60);
x_18 = x_61;
goto block_29;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_57);
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
x_62 = lean_ctor_get(x_59, 0);
x_69 = !lean_is_exclusive(x_59);
if (x_69 == 0)
{
x_63 = x_59;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_59);
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
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec(x_57);
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
x_70 = lean_ctor_get(x_58, 0);
x_77 = !lean_is_exclusive(x_58);
if (x_77 == 0)
{
x_71 = x_58;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
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
x_78 = lean_ctor_get(x_56, 0);
x_85 = !lean_is_exclusive(x_56);
if (x_85 == 0)
{
x_79 = x_56;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_56);
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
block_89:
{
if (x_87 == 0)
{
x_34 = x_87;
goto block_86;
}
else
{
x_34 = x_88;
goto block_86;
}
}
block_91:
{
if (lean_obj_tag(x_32) == 6)
{
x_88 = x_90;
goto block_89;
}
else
{
if (x_87 == 0)
{
x_34 = x_90;
goto block_86;
}
else
{
x_88 = x_90;
goto block_89;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_17, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_108);
x_109 = l_Lean_Compiler_LCNF_Simp_simp(x_108, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
lean_inc_ref(x_17);
x_111 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_17, x_110);
x_18 = x_111;
goto block_29;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
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
x_112 = lean_ctor_get(x_109, 0);
x_119 = !lean_is_exclusive(x_109);
if (x_119 == 0)
{
x_113 = x_109;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_17);
x_20 = lean_ptr_addr(x_18);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
x_24 = lean_array_fset(x_5, x_4, x_18);
lean_dec(x_4);
x_4 = x_23;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_18);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_4 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; 
x_125 = lean_ctor_get(x_7, 0);
x_126 = lean_ctor_get(x_7, 1);
x_127 = lean_ctor_get(x_7, 2);
x_128 = lean_ctor_get(x_7, 3);
x_129 = lean_ctor_get(x_7, 4);
x_130 = lean_ctor_get(x_7, 5);
x_131 = lean_ctor_get(x_7, 6);
x_132 = lean_ctor_get(x_7, 7);
x_133 = lean_ctor_get(x_7, 8);
x_134 = lean_ctor_get(x_7, 9);
x_135 = lean_ctor_get(x_7, 10);
x_136 = lean_ctor_get(x_7, 11);
x_137 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_138 = lean_ctor_get(x_7, 12);
x_139 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_140 = lean_ctor_get(x_7, 13);
x_141 = lean_nat_dec_eq(x_128, x_129);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; uint8_t x_909; 
lean_inc_ref(x_140);
lean_inc(x_138);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
lean_inc_ref(x_126);
lean_inc_ref(x_125);
x_909 = !lean_is_exclusive(x_7);
if (x_909 == 0)
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_910 = lean_ctor_get(x_7, 13);
lean_dec(x_910);
x_911 = lean_ctor_get(x_7, 12);
lean_dec(x_911);
x_912 = lean_ctor_get(x_7, 11);
lean_dec(x_912);
x_913 = lean_ctor_get(x_7, 10);
lean_dec(x_913);
x_914 = lean_ctor_get(x_7, 9);
lean_dec(x_914);
x_915 = lean_ctor_get(x_7, 8);
lean_dec(x_915);
x_916 = lean_ctor_get(x_7, 7);
lean_dec(x_916);
x_917 = lean_ctor_get(x_7, 6);
lean_dec(x_917);
x_918 = lean_ctor_get(x_7, 5);
lean_dec(x_918);
x_919 = lean_ctor_get(x_7, 4);
lean_dec(x_919);
x_920 = lean_ctor_get(x_7, 3);
lean_dec(x_920);
x_921 = lean_ctor_get(x_7, 2);
lean_dec(x_921);
x_922 = lean_ctor_get(x_7, 1);
lean_dec(x_922);
x_923 = lean_ctor_get(x_7, 0);
lean_dec(x_923);
x_142 = x_7;
x_143 = x_909;
goto block_908;
}
else
{
lean_dec(x_7);
x_142 = lean_box(0);
x_143 = x_909;
goto block_908;
}
block_908:
{
lean_object* x_144; 
x_144 = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(x_3);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; uint8_t x_898; 
x_898 = !lean_is_exclusive(x_144);
if (x_898 == 0)
{
lean_object* x_899; 
x_899 = lean_ctor_get(x_144, 0);
lean_dec(x_899);
x_145 = x_144;
x_146 = x_898;
goto block_897;
}
else
{
lean_dec(x_144);
x_145 = lean_box(0);
x_146 = x_898;
goto block_897;
}
block_897:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_128, x_221);
lean_inc(x_129);
if (x_143 == 0)
{
lean_ctor_set(x_142, 3, x_222);
x_223 = x_142;
goto block_895;
}
else
{
lean_object* x_896; 
x_896 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_896, 0, x_125);
lean_ctor_set(x_896, 1, x_126);
lean_ctor_set(x_896, 2, x_127);
lean_ctor_set(x_896, 3, x_222);
lean_ctor_set(x_896, 4, x_129);
lean_ctor_set(x_896, 5, x_130);
lean_ctor_set(x_896, 6, x_131);
lean_ctor_set(x_896, 7, x_132);
lean_ctor_set(x_896, 8, x_133);
lean_ctor_set(x_896, 9, x_134);
lean_ctor_set(x_896, 10, x_135);
lean_ctor_set(x_896, 11, x_136);
lean_ctor_set(x_896, 12, x_138);
lean_ctor_set(x_896, 13, x_140);
lean_ctor_set_uint8(x_896, sizeof(void*)*14, x_137);
lean_ctor_set_uint8(x_896, sizeof(void*)*14 + 1, x_139);
x_223 = x_896;
goto block_895;
}
block_220:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_147, 0);
x_157 = lean_ctor_get(x_147, 2);
x_158 = lean_ctor_get(x_147, 3);
x_159 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_156, x_150);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; uint8_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = 0;
x_162 = lean_unbox(x_160);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = lean_unbox(x_160);
lean_dec(x_160);
x_97 = x_164;
x_98 = x_148;
x_99 = x_147;
x_100 = x_149;
x_101 = x_150;
x_102 = x_151;
x_103 = x_152;
x_104 = x_153;
x_105 = x_154;
x_106 = x_155;
goto block_117;
}
else
{
uint8_t x_165; 
lean_inc_ref(x_158);
x_165 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_158, x_157);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = lean_unbox(x_160);
lean_dec(x_160);
x_97 = x_166;
x_98 = x_148;
x_99 = x_147;
x_100 = x_149;
x_101 = x_150;
x_102 = x_151;
x_103 = x_152;
x_104 = x_153;
x_105 = x_154;
x_106 = x_155;
goto block_117;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_st_ref_get(x_150);
x_168 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_168);
lean_dec(x_167);
x_169 = l_Lean_Compiler_LCNF_normFunDeclImp(x_161, x_141, x_147, x_168, x_152, x_153, x_154, x_155);
lean_dec_ref(x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc(x_153);
lean_inc_ref(x_152);
x_171 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_170, x_152, x_153, x_154, x_155);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_150);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec_ref(x_173);
x_174 = lean_unbox(x_160);
lean_dec(x_160);
x_97 = x_174;
x_98 = x_148;
x_99 = x_172;
x_100 = x_149;
x_101 = x_150;
x_102 = x_151;
x_103 = x_152;
x_104 = x_153;
x_105 = x_154;
x_106 = x_155;
goto block_117;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec(x_172);
lean_dec(x_160);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_1);
x_175 = lean_ctor_get(x_173, 0);
x_182 = !lean_is_exclusive(x_173);
if (x_182 == 0)
{
x_176 = x_173;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
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
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec(x_160);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_171, 0);
x_190 = !lean_is_exclusive(x_171);
if (x_190 == 0)
{
x_184 = x_171;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_171);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec(x_160);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_169, 0);
x_198 = !lean_is_exclusive(x_169);
if (x_198 == 0)
{
x_192 = x_169;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_169);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_st_ref_get(x_150);
x_200 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_200);
lean_dec(x_199);
x_201 = l_Lean_Compiler_LCNF_normFunDeclImp(x_161, x_141, x_147, x_200, x_152, x_153, x_154, x_155);
lean_dec_ref(x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = lean_unbox(x_160);
lean_dec(x_160);
x_46 = x_203;
x_47 = x_148;
x_48 = x_202;
x_49 = x_149;
x_50 = x_150;
x_51 = x_151;
x_52 = x_152;
x_53 = x_153;
x_54 = x_154;
x_55 = x_155;
goto block_96;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_211; 
lean_dec(x_160);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_1);
x_204 = lean_ctor_get(x_201, 0);
x_211 = !lean_is_exclusive(x_201);
if (x_211 == 0)
{
x_205 = x_201;
x_206 = x_211;
goto block_210;
}
else
{
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_box(0);
x_206 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_207; 
if (x_206 == 0)
{
x_207 = x_205;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_204);
x_207 = x_209;
goto block_208;
}
block_208:
{
return x_207;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_219; 
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_1);
x_212 = lean_ctor_get(x_159, 0);
x_219 = !lean_is_exclusive(x_159);
if (x_219 == 0)
{
x_213 = x_159;
x_214 = x_219;
goto block_218;
}
else
{
lean_inc(x_212);
lean_dec(x_159);
x_213 = lean_box(0);
x_214 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_215; 
if (x_214 == 0)
{
x_215 = x_213;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_212);
x_215 = x_217;
goto block_216;
}
block_216:
{
return x_215;
}
}
}
}
block_895:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_464; 
lean_del_object(x_145);
lean_dec(x_129);
lean_dec(x_128);
x_224 = lean_ctor_get(x_1, 0);
x_225 = lean_ctor_get(x_1, 1);
x_449 = 0;
lean_inc_ref(x_224);
x_464 = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(x_449, x_141, x_224, x_3, x_6);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_518; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
lean_dec_ref(x_464);
lean_inc(x_465);
lean_inc_ref(x_224);
x_518 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_449, x_224, x_465);
if (x_518 == 0)
{
goto block_517;
}
else
{
if (x_141 == 0)
{
x_466 = x_2;
x_467 = x_3;
x_468 = x_4;
x_469 = x_5;
x_470 = x_6;
x_471 = x_223;
x_472 = x_8;
goto block_507;
}
else
{
goto block_517;
}
}
block_507:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_465, 2);
x_474 = lean_ctor_get(x_465, 3);
lean_inc(x_472);
lean_inc_ref(x_471);
lean_inc(x_470);
lean_inc_ref(x_469);
lean_inc_ref(x_468);
lean_inc(x_474);
x_475 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(x_474, x_466, x_468, x_469, x_470, x_471, x_472);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
lean_dec_ref(x_475);
if (lean_obj_tag(x_476) == 1)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_467);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; 
lean_dec_ref(x_478);
x_479 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_449, x_465, x_477, x_470);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
lean_dec_ref(x_479);
x_481 = lean_ctor_get(x_480, 2);
lean_inc_ref(x_481);
x_482 = lean_ctor_get(x_480, 3);
lean_inc(x_482);
x_450 = x_480;
x_451 = x_481;
x_452 = x_482;
x_453 = x_466;
x_454 = x_467;
x_455 = x_468;
x_456 = x_469;
x_457 = x_470;
x_458 = x_471;
x_459 = x_472;
goto block_463;
}
else
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_490; 
lean_dec(x_472);
lean_dec_ref(x_471);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_1);
x_483 = lean_ctor_get(x_479, 0);
x_490 = !lean_is_exclusive(x_479);
if (x_490 == 0)
{
x_484 = x_479;
x_485 = x_490;
goto block_489;
}
else
{
lean_inc(x_483);
lean_dec(x_479);
x_484 = lean_box(0);
x_485 = x_490;
goto block_489;
}
block_489:
{
lean_object* x_486; 
if (x_485 == 0)
{
x_486 = x_484;
goto block_487;
}
else
{
lean_object* x_488; 
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_483);
x_486 = x_488;
goto block_487;
}
block_487:
{
return x_486;
}
}
}
}
else
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; uint8_t x_498; 
lean_dec(x_477);
lean_dec(x_472);
lean_dec_ref(x_471);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_1);
x_491 = lean_ctor_get(x_478, 0);
x_498 = !lean_is_exclusive(x_478);
if (x_498 == 0)
{
x_492 = x_478;
x_493 = x_498;
goto block_497;
}
else
{
lean_inc(x_491);
lean_dec(x_478);
x_492 = lean_box(0);
x_493 = x_498;
goto block_497;
}
block_497:
{
lean_object* x_494; 
if (x_493 == 0)
{
x_494 = x_492;
goto block_495;
}
else
{
lean_object* x_496; 
x_496 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_496, 0, x_491);
x_494 = x_496;
goto block_495;
}
block_495:
{
return x_494;
}
}
}
}
else
{
lean_inc(x_474);
lean_inc_ref(x_473);
lean_dec(x_476);
x_450 = x_465;
x_451 = x_473;
x_452 = x_474;
x_453 = x_466;
x_454 = x_467;
x_455 = x_468;
x_456 = x_469;
x_457 = x_470;
x_458 = x_471;
x_459 = x_472;
goto block_463;
}
}
else
{
lean_object* x_499; lean_object* x_500; uint8_t x_501; uint8_t x_506; 
lean_dec(x_472);
lean_dec_ref(x_471);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_1);
x_499 = lean_ctor_get(x_475, 0);
x_506 = !lean_is_exclusive(x_475);
if (x_506 == 0)
{
x_500 = x_475;
x_501 = x_506;
goto block_505;
}
else
{
lean_inc(x_499);
lean_dec(x_475);
x_500 = lean_box(0);
x_501 = x_506;
goto block_505;
}
block_505:
{
lean_object* x_502; 
if (x_501 == 0)
{
x_502 = x_500;
goto block_503;
}
else
{
lean_object* x_504; 
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_499);
x_502 = x_504;
goto block_503;
}
block_503:
{
return x_502;
}
}
}
}
block_517:
{
lean_object* x_508; 
x_508 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
if (lean_obj_tag(x_508) == 0)
{
lean_dec_ref(x_508);
x_466 = x_2;
x_467 = x_3;
x_468 = x_4;
x_469 = x_5;
x_470 = x_6;
x_471 = x_223;
x_472 = x_8;
goto block_507;
}
else
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_516; 
lean_dec(x_465);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_509 = lean_ctor_get(x_508, 0);
x_516 = !lean_is_exclusive(x_508);
if (x_516 == 0)
{
x_510 = x_508;
x_511 = x_516;
goto block_515;
}
else
{
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_box(0);
x_511 = x_516;
goto block_515;
}
block_515:
{
lean_object* x_512; 
if (x_511 == 0)
{
x_512 = x_510;
goto block_513;
}
else
{
lean_object* x_514; 
x_514 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_514, 0, x_509);
x_512 = x_514;
goto block_513;
}
block_513:
{
return x_512;
}
}
}
}
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; uint8_t x_526; 
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_519 = lean_ctor_get(x_464, 0);
x_526 = !lean_is_exclusive(x_464);
if (x_526 == 0)
{
x_520 = x_464;
x_521 = x_526;
goto block_525;
}
else
{
lean_inc(x_519);
lean_dec(x_464);
x_520 = lean_box(0);
x_521 = x_526;
goto block_525;
}
block_525:
{
lean_object* x_522; 
if (x_521 == 0)
{
x_522 = x_520;
goto block_523;
}
else
{
lean_object* x_524; 
x_524 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_524, 0, x_519);
x_522 = x_524;
goto block_523;
}
block_523:
{
return x_522;
}
}
}
block_448:
{
if (x_234 == 0)
{
lean_object* x_235; 
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_233);
x_235 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_233, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
if (lean_obj_tag(x_236) == 1)
{
lean_object* x_237; lean_object* x_238; 
lean_inc_ref(x_225);
lean_dec_ref(x_233);
lean_dec_ref(x_1);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_232);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
lean_dec_ref(x_238);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_230);
lean_inc(x_232);
lean_inc_ref(x_227);
x_239 = l_Lean_Compiler_LCNF_Simp_simp(x_225, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_237, x_240, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec(x_229);
lean_dec_ref(x_226);
lean_dec_ref(x_230);
lean_dec(x_232);
lean_dec_ref(x_227);
lean_dec(x_237);
return x_241;
}
else
{
lean_dec(x_237);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
return x_239;
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec(x_237);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_242 = lean_ctor_get(x_238, 0);
x_249 = !lean_is_exclusive(x_238);
if (x_249 == 0)
{
x_243 = x_238;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_box(0);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_244 == 0)
{
x_245 = x_243;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_242);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
else
{
lean_object* x_250; 
lean_dec(x_236);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_233);
x_250 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_233, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
if (lean_obj_tag(x_251) == 1)
{
lean_object* x_252; uint8_t x_253; uint8_t x_260; 
lean_inc_ref(x_225);
lean_dec_ref(x_233);
x_260 = !lean_is_exclusive(x_1);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_1, 1);
lean_dec(x_261);
x_262 = lean_ctor_get(x_1, 0);
lean_dec(x_262);
x_252 = x_1;
x_253 = x_260;
goto block_259;
}
else
{
lean_dec(x_1);
x_252 = lean_box(0);
x_253 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_251, 0);
lean_inc(x_254);
lean_dec_ref(x_251);
if (x_253 == 0)
{
lean_ctor_set_tag(x_252, 1);
lean_ctor_set(x_252, 0, x_254);
x_255 = x_252;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_225);
x_255 = x_258;
goto block_257;
}
block_257:
{
x_1 = x_255;
x_2 = x_227;
x_3 = x_232;
x_4 = x_230;
x_5 = x_226;
x_6 = x_229;
x_7 = x_228;
x_8 = x_231;
goto _start;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_251);
x_263 = lean_ctor_get(x_233, 0);
x_264 = lean_ctor_get(x_233, 3);
x_265 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
if (lean_obj_tag(x_266) == 1)
{
lean_object* x_267; lean_object* x_268; 
lean_inc_ref(x_225);
lean_dec_ref(x_1);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
lean_inc(x_263);
x_268 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_263, x_267, x_232, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
lean_dec_ref(x_268);
x_269 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_233, x_232, x_229);
lean_dec_ref(x_233);
if (lean_obj_tag(x_269) == 0)
{
lean_dec_ref(x_269);
x_1 = x_225;
x_2 = x_227;
x_3 = x_232;
x_4 = x_230;
x_5 = x_226;
x_6 = x_229;
x_7 = x_228;
x_8 = x_231;
goto _start;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_271 = lean_ctor_get(x_269, 0);
x_278 = !lean_is_exclusive(x_269);
if (x_278 == 0)
{
x_272 = x_269;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_269);
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
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; uint8_t x_286; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_279 = lean_ctor_get(x_268, 0);
x_286 = !lean_is_exclusive(x_268);
if (x_286 == 0)
{
x_280 = x_268;
x_281 = x_286;
goto block_285;
}
else
{
lean_inc(x_279);
lean_dec(x_268);
x_280 = lean_box(0);
x_281 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_282; 
if (x_281 == 0)
{
x_282 = x_280;
goto block_283;
}
else
{
lean_object* x_284; 
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_279);
x_282 = x_284;
goto block_283;
}
block_283:
{
return x_282;
}
}
}
}
else
{
lean_object* x_287; 
lean_dec(x_266);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_230);
lean_inc(x_232);
lean_inc_ref(x_227);
lean_inc_ref(x_225);
lean_inc_ref(x_233);
x_287 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_233, x_225, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
if (lean_obj_tag(x_288) == 1)
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_233, x_232, x_229);
lean_dec(x_229);
lean_dec(x_232);
lean_dec_ref(x_233);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; uint8_t x_292; uint8_t x_297; 
x_297 = !lean_is_exclusive(x_290);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_290, 0);
lean_dec(x_298);
x_291 = x_290;
x_292 = x_297;
goto block_296;
}
else
{
lean_dec(x_290);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
lean_ctor_set(x_291, 0, x_289);
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_289);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_306; 
lean_dec(x_289);
x_299 = lean_ctor_get(x_290, 0);
x_306 = !lean_is_exclusive(x_290);
if (x_306 == 0)
{
x_300 = x_290;
x_301 = x_306;
goto block_305;
}
else
{
lean_inc(x_299);
lean_dec(x_290);
x_300 = lean_box(0);
x_301 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_302; 
if (x_301 == 0)
{
x_302 = x_300;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_299);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
else
{
lean_object* x_307; 
lean_dec(x_288);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_230);
lean_inc(x_232);
lean_inc_ref(x_227);
lean_inc(x_264);
x_307 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_264, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
if (lean_obj_tag(x_308) == 1)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_inc_ref(x_225);
lean_dec_ref(x_1);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_263);
x_312 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_263, x_311, x_232, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
lean_dec_ref(x_312);
x_313 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_233, x_232, x_229);
lean_dec_ref(x_233);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
lean_dec_ref(x_313);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_230);
lean_inc(x_232);
lean_inc_ref(x_227);
x_314 = l_Lean_Compiler_LCNF_Simp_simp(x_225, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec_ref(x_314);
x_316 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_310, x_315, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec(x_229);
lean_dec_ref(x_226);
lean_dec_ref(x_230);
lean_dec(x_232);
lean_dec_ref(x_227);
lean_dec(x_310);
return x_316;
}
else
{
lean_dec(x_310);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
return x_314;
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_324; 
lean_dec(x_310);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_317 = lean_ctor_get(x_313, 0);
x_324 = !lean_is_exclusive(x_313);
if (x_324 == 0)
{
x_318 = x_313;
x_319 = x_324;
goto block_323;
}
else
{
lean_inc(x_317);
lean_dec(x_313);
x_318 = lean_box(0);
x_319 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_320; 
if (x_319 == 0)
{
x_320 = x_318;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_317);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_332; 
lean_dec(x_310);
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_325 = lean_ctor_get(x_312, 0);
x_332 = !lean_is_exclusive(x_312);
if (x_332 == 0)
{
x_326 = x_312;
x_327 = x_332;
goto block_331;
}
else
{
lean_inc(x_325);
lean_dec(x_312);
x_326 = lean_box(0);
x_327 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_328; 
if (x_327 == 0)
{
x_328 = x_326;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_325);
x_328 = x_330;
goto block_329;
}
block_329:
{
return x_328;
}
}
}
}
else
{
lean_object* x_333; 
lean_dec(x_308);
lean_inc(x_231);
lean_inc_ref(x_228);
lean_inc(x_229);
lean_inc_ref(x_226);
lean_inc_ref(x_230);
lean_inc(x_232);
lean_inc_ref(x_227);
lean_inc_ref(x_225);
x_333 = l_Lean_Compiler_LCNF_Simp_simp(x_225, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_dec_ref(x_333);
x_335 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_263, x_232);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; 
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_338 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_233, x_232, x_229);
lean_dec(x_229);
lean_dec(x_232);
lean_dec_ref(x_233);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; uint8_t x_345; 
x_345 = !lean_is_exclusive(x_338);
if (x_345 == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_338, 0);
lean_dec(x_346);
x_339 = x_338;
x_340 = x_345;
goto block_344;
}
else
{
lean_dec(x_338);
x_339 = lean_box(0);
x_340 = x_345;
goto block_344;
}
block_344:
{
lean_object* x_341; 
if (x_340 == 0)
{
lean_ctor_set(x_339, 0, x_334);
x_341 = x_339;
goto block_342;
}
else
{
lean_object* x_343; 
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_334);
x_341 = x_343;
goto block_342;
}
block_342:
{
return x_341;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_354; 
lean_dec(x_334);
x_347 = lean_ctor_get(x_338, 0);
x_354 = !lean_is_exclusive(x_338);
if (x_354 == 0)
{
x_348 = x_338;
x_349 = x_354;
goto block_353;
}
else
{
lean_inc(x_347);
lean_dec(x_338);
x_348 = lean_box(0);
x_349 = x_354;
goto block_353;
}
block_353:
{
lean_object* x_350; 
if (x_349 == 0)
{
x_350 = x_348;
goto block_351;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_347);
x_350 = x_352;
goto block_351;
}
block_351:
{
return x_350;
}
}
}
}
else
{
lean_object* x_355; 
lean_inc_ref(x_233);
x_355 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_233, x_227, x_232, x_230, x_226, x_229, x_228, x_231);
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec(x_229);
lean_dec_ref(x_226);
lean_dec_ref(x_230);
lean_dec(x_232);
lean_dec_ref(x_227);
if (lean_obj_tag(x_355) == 0)
{
size_t x_356; size_t x_357; uint8_t x_358; 
lean_dec_ref(x_355);
x_356 = lean_ptr_addr(x_225);
x_357 = lean_ptr_addr(x_334);
x_358 = lean_usize_dec_eq(x_356, x_357);
if (x_358 == 0)
{
x_118 = x_334;
x_119 = x_233;
x_120 = x_358;
goto block_124;
}
else
{
size_t x_359; size_t x_360; uint8_t x_361; 
x_359 = lean_ptr_addr(x_224);
x_360 = lean_ptr_addr(x_233);
x_361 = lean_usize_dec_eq(x_359, x_360);
x_118 = x_334;
x_119 = x_233;
x_120 = x_361;
goto block_124;
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_369; 
lean_dec(x_334);
lean_dec_ref(x_233);
lean_dec_ref(x_1);
x_362 = lean_ctor_get(x_355, 0);
x_369 = !lean_is_exclusive(x_355);
if (x_369 == 0)
{
x_363 = x_355;
x_364 = x_369;
goto block_368;
}
else
{
lean_inc(x_362);
lean_dec(x_355);
x_363 = lean_box(0);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_364 == 0)
{
x_365 = x_363;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_362);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_377; 
lean_dec(x_334);
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_370 = lean_ctor_get(x_335, 0);
x_377 = !lean_is_exclusive(x_335);
if (x_377 == 0)
{
x_371 = x_335;
x_372 = x_377;
goto block_376;
}
else
{
lean_inc(x_370);
lean_dec(x_335);
x_371 = lean_box(0);
x_372 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_373; 
if (x_372 == 0)
{
x_373 = x_371;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_370);
x_373 = x_375;
goto block_374;
}
block_374:
{
return x_373;
}
}
}
}
else
{
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
return x_333;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_385; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_378 = lean_ctor_get(x_307, 0);
x_385 = !lean_is_exclusive(x_307);
if (x_385 == 0)
{
x_379 = x_307;
x_380 = x_385;
goto block_384;
}
else
{
lean_inc(x_378);
lean_dec(x_307);
x_379 = lean_box(0);
x_380 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_381; 
if (x_380 == 0)
{
x_381 = x_379;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_378);
x_381 = x_383;
goto block_382;
}
block_382:
{
return x_381;
}
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; uint8_t x_393; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_386 = lean_ctor_get(x_287, 0);
x_393 = !lean_is_exclusive(x_287);
if (x_393 == 0)
{
x_387 = x_287;
x_388 = x_393;
goto block_392;
}
else
{
lean_inc(x_386);
lean_dec(x_287);
x_387 = lean_box(0);
x_388 = x_393;
goto block_392;
}
block_392:
{
lean_object* x_389; 
if (x_388 == 0)
{
x_389 = x_387;
goto block_390;
}
else
{
lean_object* x_391; 
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_386);
x_389 = x_391;
goto block_390;
}
block_390:
{
return x_389;
}
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; uint8_t x_401; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_394 = lean_ctor_get(x_265, 0);
x_401 = !lean_is_exclusive(x_265);
if (x_401 == 0)
{
x_395 = x_265;
x_396 = x_401;
goto block_400;
}
else
{
lean_inc(x_394);
lean_dec(x_265);
x_395 = lean_box(0);
x_396 = x_401;
goto block_400;
}
block_400:
{
lean_object* x_397; 
if (x_396 == 0)
{
x_397 = x_395;
goto block_398;
}
else
{
lean_object* x_399; 
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_394);
x_397 = x_399;
goto block_398;
}
block_398:
{
return x_397;
}
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_409; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_402 = lean_ctor_get(x_250, 0);
x_409 = !lean_is_exclusive(x_250);
if (x_409 == 0)
{
x_403 = x_250;
x_404 = x_409;
goto block_408;
}
else
{
lean_inc(x_402);
lean_dec(x_250);
x_403 = lean_box(0);
x_404 = x_409;
goto block_408;
}
block_408:
{
lean_object* x_405; 
if (x_404 == 0)
{
x_405 = x_403;
goto block_406;
}
else
{
lean_object* x_407; 
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_402);
x_405 = x_407;
goto block_406;
}
block_406:
{
return x_405;
}
}
}
}
}
else
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_417; 
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_235, 0);
x_417 = !lean_is_exclusive(x_235);
if (x_417 == 0)
{
x_411 = x_235;
x_412 = x_417;
goto block_416;
}
else
{
lean_inc(x_410);
lean_dec(x_235);
x_411 = lean_box(0);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
if (x_412 == 0)
{
x_413 = x_411;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_410);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; uint8_t x_447; 
lean_inc_ref(x_225);
lean_dec_ref(x_1);
x_418 = lean_st_ref_take(x_232);
x_419 = lean_ctor_get(x_233, 0);
x_420 = lean_ctor_get(x_418, 0);
x_421 = lean_ctor_get(x_418, 1);
x_422 = lean_ctor_get(x_418, 2);
x_423 = lean_ctor_get(x_418, 3);
x_424 = lean_ctor_get_uint8(x_418, sizeof(void*)*7);
x_425 = lean_ctor_get(x_418, 4);
x_426 = lean_ctor_get(x_418, 5);
x_427 = lean_ctor_get(x_418, 6);
x_447 = !lean_is_exclusive(x_418);
if (x_447 == 0)
{
x_428 = x_418;
x_429 = x_447;
goto block_446;
}
else
{
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_418);
x_428 = lean_box(0);
x_429 = x_447;
goto block_446;
}
block_446:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_box(0);
lean_inc(x_419);
x_431 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_420, x_419, x_430);
if (x_429 == 0)
{
lean_ctor_set(x_428, 0, x_431);
x_432 = x_428;
goto block_444;
}
else
{
lean_object* x_445; 
x_445 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_445, 0, x_431);
lean_ctor_set(x_445, 1, x_421);
lean_ctor_set(x_445, 2, x_422);
lean_ctor_set(x_445, 3, x_423);
lean_ctor_set(x_445, 4, x_425);
lean_ctor_set(x_445, 5, x_426);
lean_ctor_set(x_445, 6, x_427);
lean_ctor_set_uint8(x_445, sizeof(void*)*7, x_424);
x_432 = x_445;
goto block_444;
}
block_444:
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_st_ref_set(x_232, x_432);
x_434 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(x_233, x_232, x_229);
lean_dec_ref(x_233);
if (lean_obj_tag(x_434) == 0)
{
lean_dec_ref(x_434);
x_1 = x_225;
x_2 = x_227;
x_3 = x_232;
x_4 = x_230;
x_5 = x_226;
x_6 = x_229;
x_7 = x_228;
x_8 = x_231;
goto _start;
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; uint8_t x_443; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
x_436 = lean_ctor_get(x_434, 0);
x_443 = !lean_is_exclusive(x_434);
if (x_443 == 0)
{
x_437 = x_434;
x_438 = x_443;
goto block_442;
}
else
{
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_box(0);
x_438 = x_443;
goto block_442;
}
block_442:
{
lean_object* x_439; 
if (x_438 == 0)
{
x_439 = x_437;
goto block_440;
}
else
{
lean_object* x_441; 
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_436);
x_439 = x_441;
goto block_440;
}
block_440:
{
return x_439;
}
}
}
}
}
}
}
block_463:
{
uint8_t x_460; 
x_460 = l_Lean_Expr_isErased(x_451);
lean_dec_ref(x_451);
if (x_460 == 0)
{
lean_dec(x_452);
x_226 = x_456;
x_227 = x_453;
x_228 = x_458;
x_229 = x_457;
x_230 = x_455;
x_231 = x_459;
x_232 = x_454;
x_233 = x_450;
x_234 = x_141;
goto block_448;
}
else
{
lean_object* x_461; uint8_t x_462; 
x_461 = lean_box(1);
x_462 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_449, x_452, x_461);
if (x_462 == 0)
{
x_226 = x_456;
x_227 = x_453;
x_228 = x_458;
x_229 = x_457;
x_230 = x_455;
x_231 = x_459;
x_232 = x_454;
x_233 = x_450;
x_234 = x_460;
goto block_448;
}
else
{
x_226 = x_456;
x_227 = x_453;
x_228 = x_458;
x_229 = x_457;
x_230 = x_455;
x_231 = x_459;
x_232 = x_454;
x_233 = x_450;
x_234 = x_141;
goto block_448;
}
}
}
}
case 3:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; 
lean_del_object(x_145);
lean_dec(x_129);
lean_dec(x_128);
x_527 = lean_ctor_get(x_1, 0);
x_528 = lean_ctor_get(x_1, 1);
x_529 = lean_st_ref_get(x_3);
x_530 = lean_ctor_get(x_529, 0);
lean_inc_ref(x_530);
lean_dec(x_529);
x_531 = 0;
lean_inc(x_527);
x_532 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_530, x_527, x_141);
lean_dec_ref(x_530);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
lean_dec_ref(x_532);
lean_inc_ref(x_528);
x_534 = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(x_531, x_141, x_528, x_3);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; uint8_t x_603; 
x_535 = lean_ctor_get(x_534, 0);
x_603 = !lean_is_exclusive(x_534);
if (x_603 == 0)
{
x_536 = x_534;
x_537 = x_603;
goto block_602;
}
else
{
lean_inc(x_535);
lean_dec(x_534);
x_536 = lean_box(0);
x_537 = x_603;
goto block_602;
}
block_602:
{
uint8_t x_538; lean_object* x_560; lean_object* x_570; 
lean_inc(x_8);
lean_inc_ref(x_223);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_535);
x_570 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_533, x_535, x_2, x_3, x_4, x_5, x_6, x_223, x_8);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
lean_dec_ref(x_570);
if (lean_obj_tag(x_571) == 1)
{
lean_object* x_572; 
lean_del_object(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_1 = x_572;
x_7 = x_223;
goto _start;
}
else
{
lean_object* x_574; 
lean_dec(x_571);
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc(x_533);
x_574 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_533, x_3);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; uint8_t x_577; 
lean_dec_ref(x_574);
x_575 = lean_unsigned_to_nat(0u);
x_576 = lean_array_get_size(x_535);
x_577 = lean_nat_dec_lt(x_575, x_576);
if (x_577 == 0)
{
lean_dec(x_3);
goto block_559;
}
else
{
lean_object* x_578; uint8_t x_579; 
x_578 = lean_box(0);
x_579 = lean_nat_dec_le(x_576, x_576);
if (x_579 == 0)
{
if (x_577 == 0)
{
lean_dec(x_3);
goto block_559;
}
else
{
size_t x_580; size_t x_581; lean_object* x_582; 
x_580 = 0;
x_581 = lean_usize_of_nat(x_576);
x_582 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_535, x_580, x_581, x_578, x_3);
lean_dec(x_3);
x_560 = x_582;
goto block_569;
}
}
else
{
size_t x_583; size_t x_584; lean_object* x_585; 
x_583 = 0;
x_584 = lean_usize_of_nat(x_576);
x_585 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(x_535, x_583, x_584, x_578, x_3);
lean_dec(x_3);
x_560 = x_585;
goto block_569;
}
}
}
else
{
lean_object* x_586; lean_object* x_587; uint8_t x_588; uint8_t x_593; 
lean_del_object(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
lean_dec(x_3);
x_586 = lean_ctor_get(x_574, 0);
x_593 = !lean_is_exclusive(x_574);
if (x_593 == 0)
{
x_587 = x_574;
x_588 = x_593;
goto block_592;
}
else
{
lean_inc(x_586);
lean_dec(x_574);
x_587 = lean_box(0);
x_588 = x_593;
goto block_592;
}
block_592:
{
lean_object* x_589; 
if (x_588 == 0)
{
x_589 = x_587;
goto block_590;
}
else
{
lean_object* x_591; 
x_591 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_591, 0, x_586);
x_589 = x_591;
goto block_590;
}
block_590:
{
return x_589;
}
}
}
}
}
else
{
lean_object* x_594; lean_object* x_595; uint8_t x_596; uint8_t x_601; 
lean_del_object(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_594 = lean_ctor_get(x_570, 0);
x_601 = !lean_is_exclusive(x_570);
if (x_601 == 0)
{
x_595 = x_570;
x_596 = x_601;
goto block_600;
}
else
{
lean_inc(x_594);
lean_dec(x_570);
x_595 = lean_box(0);
x_596 = x_601;
goto block_600;
}
block_600:
{
lean_object* x_597; 
if (x_596 == 0)
{
x_597 = x_595;
goto block_598;
}
else
{
lean_object* x_599; 
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_594);
x_597 = x_599;
goto block_598;
}
block_598:
{
return x_597;
}
}
}
block_554:
{
if (x_538 == 0)
{
lean_object* x_539; uint8_t x_540; uint8_t x_548; 
x_548 = !lean_is_exclusive(x_1);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_ctor_get(x_1, 1);
lean_dec(x_549);
x_550 = lean_ctor_get(x_1, 0);
lean_dec(x_550);
x_539 = x_1;
x_540 = x_548;
goto block_547;
}
else
{
lean_dec(x_1);
x_539 = lean_box(0);
x_540 = x_548;
goto block_547;
}
block_547:
{
lean_object* x_541; 
if (x_540 == 0)
{
lean_ctor_set(x_539, 1, x_535);
lean_ctor_set(x_539, 0, x_533);
x_541 = x_539;
goto block_545;
}
else
{
lean_object* x_546; 
x_546 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_546, 0, x_533);
lean_ctor_set(x_546, 1, x_535);
x_541 = x_546;
goto block_545;
}
block_545:
{
lean_object* x_542; 
if (x_537 == 0)
{
lean_ctor_set(x_536, 0, x_541);
x_542 = x_536;
goto block_543;
}
else
{
lean_object* x_544; 
x_544 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_544, 0, x_541);
x_542 = x_544;
goto block_543;
}
block_543:
{
return x_542;
}
}
}
}
else
{
lean_object* x_551; 
lean_dec(x_535);
lean_dec(x_533);
if (x_537 == 0)
{
lean_ctor_set(x_536, 0, x_1);
x_551 = x_536;
goto block_552;
}
else
{
lean_object* x_553; 
x_553 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_553, 0, x_1);
x_551 = x_553;
goto block_552;
}
block_552:
{
return x_551;
}
}
}
block_559:
{
uint8_t x_555; 
x_555 = l_Lean_instBEqFVarId_beq(x_527, x_533);
if (x_555 == 0)
{
x_538 = x_555;
goto block_554;
}
else
{
size_t x_556; size_t x_557; uint8_t x_558; 
x_556 = lean_ptr_addr(x_528);
x_557 = lean_ptr_addr(x_535);
x_558 = lean_usize_dec_eq(x_556, x_557);
x_538 = x_558;
goto block_554;
}
}
block_569:
{
if (lean_obj_tag(x_560) == 0)
{
lean_dec_ref(x_560);
goto block_559;
}
else
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; uint8_t x_568; 
lean_del_object(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
x_561 = lean_ctor_get(x_560, 0);
x_568 = !lean_is_exclusive(x_560);
if (x_568 == 0)
{
x_562 = x_560;
x_563 = x_568;
goto block_567;
}
else
{
lean_inc(x_561);
lean_dec(x_560);
x_562 = lean_box(0);
x_563 = x_568;
goto block_567;
}
block_567:
{
lean_object* x_564; 
if (x_563 == 0)
{
x_564 = x_562;
goto block_565;
}
else
{
lean_object* x_566; 
x_566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_566, 0, x_561);
x_564 = x_566;
goto block_565;
}
block_565:
{
return x_564;
}
}
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; uint8_t x_606; uint8_t x_611; 
lean_dec(x_533);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_604 = lean_ctor_get(x_534, 0);
x_611 = !lean_is_exclusive(x_534);
if (x_611 == 0)
{
x_605 = x_534;
x_606 = x_611;
goto block_610;
}
else
{
lean_inc(x_604);
lean_dec(x_534);
x_605 = lean_box(0);
x_606 = x_611;
goto block_610;
}
block_610:
{
lean_object* x_607; 
if (x_606 == 0)
{
x_607 = x_605;
goto block_608;
}
else
{
lean_object* x_609; 
x_609 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_609, 0, x_604);
x_607 = x_609;
goto block_608;
}
block_608:
{
return x_607;
}
}
}
}
else
{
lean_object* x_612; 
lean_dec_ref(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_612 = l_Lean_Compiler_LCNF_mkReturnErased(x_531, x_5, x_6, x_223, x_8);
lean_dec(x_8);
lean_dec_ref(x_223);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_612;
}
}
case 4:
{
lean_object* x_613; lean_object* x_614; 
lean_del_object(x_145);
x_613 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_613);
lean_inc(x_8);
lean_inc_ref(x_223);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_613);
x_614 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_613, x_2, x_3, x_4, x_5, x_6, x_223, x_8);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; uint8_t x_617; uint8_t x_826; 
x_615 = lean_ctor_get(x_614, 0);
x_826 = !lean_is_exclusive(x_614);
if (x_826 == 0)
{
x_616 = x_614;
x_617 = x_826;
goto block_825;
}
else
{
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_box(0);
x_617 = x_826;
goto block_825;
}
block_825:
{
if (lean_obj_tag(x_615) == 1)
{
lean_object* x_618; lean_object* x_619; 
lean_dec_ref(x_613);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_618 = lean_ctor_get(x_615, 0);
lean_inc(x_618);
lean_dec_ref(x_615);
if (x_617 == 0)
{
lean_ctor_set(x_616, 0, x_618);
x_619 = x_616;
goto block_620;
}
else
{
lean_object* x_621; 
x_621 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_621, 0, x_618);
x_619 = x_621;
goto block_620;
}
block_620:
{
return x_619;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; uint8_t x_824; 
lean_dec(x_615);
x_622 = lean_ctor_get(x_613, 0);
x_623 = lean_ctor_get(x_613, 1);
x_624 = lean_ctor_get(x_613, 2);
x_625 = lean_ctor_get(x_613, 3);
x_824 = !lean_is_exclusive(x_613);
if (x_824 == 0)
{
x_626 = x_613;
x_627 = x_824;
goto block_823;
}
else
{
lean_inc(x_625);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_613);
x_626 = lean_box(0);
x_627 = x_824;
goto block_823;
}
block_823:
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; 
x_628 = lean_st_ref_get(x_3);
x_629 = lean_ctor_get(x_628, 0);
lean_inc_ref(x_629);
lean_dec(x_628);
x_630 = 0;
lean_inc(x_624);
x_631 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_629, x_624, x_141);
lean_dec_ref(x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; uint8_t x_634; uint8_t x_821; 
x_632 = lean_ctor_get(x_631, 0);
x_821 = !lean_is_exclusive(x_631);
if (x_821 == 0)
{
x_633 = x_631;
x_634 = x_821;
goto block_820;
}
else
{
lean_inc(x_632);
lean_dec(x_631);
x_633 = lean_box(0);
x_634 = x_821;
goto block_820;
}
block_820:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_st_ref_get(x_3);
x_636 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_223);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_625);
lean_inc(x_632);
x_637 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(x_632, x_128, x_129, x_636, x_625, x_2, x_3, x_4, x_5, x_6, x_223, x_8);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; lean_object* x_639; uint8_t x_640; uint8_t x_811; 
x_638 = lean_ctor_get(x_637, 0);
x_811 = !lean_is_exclusive(x_637);
if (x_811 == 0)
{
x_639 = x_637;
x_640 = x_811;
goto block_810;
}
else
{
lean_inc(x_638);
lean_dec(x_637);
x_639 = lean_box(0);
x_640 = x_811;
goto block_810;
}
block_810:
{
lean_object* x_641; 
lean_inc(x_8);
lean_inc_ref(x_223);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_641 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_638, x_2, x_3, x_4, x_5, x_6, x_223, x_8);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; uint8_t x_801; 
x_642 = lean_ctor_get(x_641, 0);
x_801 = !lean_is_exclusive(x_641);
if (x_801 == 0)
{
x_643 = x_641;
x_644 = x_801;
goto block_800;
}
else
{
lean_inc(x_642);
lean_dec(x_641);
x_643 = lean_box(0);
x_644 = x_801;
goto block_800;
}
block_800:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_669; lean_object* x_670; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_704; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_736; uint8_t x_737; 
x_645 = lean_ctor_get(x_635, 0);
lean_inc_ref(x_645);
lean_dec(x_635);
lean_inc_ref(x_623);
x_646 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_630, x_645, x_141, x_623);
lean_dec_ref(x_645);
x_736 = lean_array_get_size(x_642);
x_737 = lean_nat_dec_eq(x_736, x_221);
if (x_737 == 0)
{
lean_del_object(x_616);
x_710 = x_3;
x_711 = x_5;
x_712 = x_6;
x_713 = x_223;
x_714 = x_8;
goto block_735;
}
else
{
lean_object* x_738; 
x_738 = lean_array_fget_borrowed(x_642, x_636);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_759; lean_object* x_769; uint8_t x_780; uint8_t x_782; 
lean_del_object(x_616);
x_739 = lean_ctor_get(x_738, 1);
x_740 = lean_ctor_get(x_738, 2);
x_769 = lean_array_get_size(x_739);
x_782 = lean_nat_dec_lt(x_636, x_769);
if (x_782 == 0)
{
x_780 = x_141;
goto block_781;
}
else
{
if (x_782 == 0)
{
x_780 = x_141;
goto block_781;
}
else
{
size_t x_783; size_t x_784; lean_object* x_785; 
x_783 = 0;
x_784 = lean_usize_of_nat(x_769);
x_785 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(x_739, x_783, x_784, x_3);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; uint8_t x_787; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
lean_dec_ref(x_785);
x_787 = lean_unbox(x_786);
lean_dec(x_786);
x_780 = x_787;
goto block_781;
}
else
{
lean_object* x_788; lean_object* x_789; uint8_t x_790; uint8_t x_795; 
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_del_object(x_639);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_788 = lean_ctor_get(x_785, 0);
x_795 = !lean_is_exclusive(x_785);
if (x_795 == 0)
{
x_789 = x_785;
x_790 = x_795;
goto block_794;
}
else
{
lean_inc(x_788);
lean_dec(x_785);
x_789 = lean_box(0);
x_790 = x_795;
goto block_794;
}
block_794:
{
lean_object* x_791; 
if (x_790 == 0)
{
x_791 = x_789;
goto block_792;
}
else
{
lean_object* x_793; 
x_793 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_793, 0, x_788);
x_791 = x_793;
goto block_792;
}
block_792:
{
return x_791;
}
}
}
}
}
block_758:
{
lean_object* x_741; 
x_741 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; uint8_t x_743; uint8_t x_748; 
x_748 = !lean_is_exclusive(x_741);
if (x_748 == 0)
{
lean_object* x_749; 
x_749 = lean_ctor_get(x_741, 0);
lean_dec(x_749);
x_742 = x_741;
x_743 = x_748;
goto block_747;
}
else
{
lean_dec(x_741);
x_742 = lean_box(0);
x_743 = x_748;
goto block_747;
}
block_747:
{
lean_object* x_744; 
if (x_743 == 0)
{
lean_ctor_set(x_742, 0, x_740);
x_744 = x_742;
goto block_745;
}
else
{
lean_object* x_746; 
x_746 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_746, 0, x_740);
x_744 = x_746;
goto block_745;
}
block_745:
{
return x_744;
}
}
}
else
{
lean_object* x_750; lean_object* x_751; uint8_t x_752; uint8_t x_757; 
lean_dec_ref(x_740);
x_750 = lean_ctor_get(x_741, 0);
x_757 = !lean_is_exclusive(x_741);
if (x_757 == 0)
{
x_751 = x_741;
x_752 = x_757;
goto block_756;
}
else
{
lean_inc(x_750);
lean_dec(x_741);
x_751 = lean_box(0);
x_752 = x_757;
goto block_756;
}
block_756:
{
lean_object* x_753; 
if (x_752 == 0)
{
x_753 = x_751;
goto block_754;
}
else
{
lean_object* x_755; 
x_755 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_755, 0, x_750);
x_753 = x_755;
goto block_754;
}
block_754:
{
return x_753;
}
}
}
}
block_768:
{
if (lean_obj_tag(x_759) == 0)
{
lean_dec_ref(x_759);
goto block_758;
}
else
{
lean_object* x_760; lean_object* x_761; uint8_t x_762; uint8_t x_767; 
lean_dec_ref(x_740);
lean_dec(x_3);
x_760 = lean_ctor_get(x_759, 0);
x_767 = !lean_is_exclusive(x_759);
if (x_767 == 0)
{
x_761 = x_759;
x_762 = x_767;
goto block_766;
}
else
{
lean_inc(x_760);
lean_dec(x_759);
x_761 = lean_box(0);
x_762 = x_767;
goto block_766;
}
block_766:
{
lean_object* x_763; 
if (x_762 == 0)
{
x_763 = x_761;
goto block_764;
}
else
{
lean_object* x_765; 
x_765 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_765, 0, x_760);
x_763 = x_765;
goto block_764;
}
block_764:
{
return x_763;
}
}
}
}
block_779:
{
uint8_t x_770; 
x_770 = lean_nat_dec_lt(x_636, x_769);
if (x_770 == 0)
{
lean_dec_ref(x_739);
lean_dec(x_6);
goto block_758;
}
else
{
lean_object* x_771; uint8_t x_772; 
x_771 = lean_box(0);
x_772 = lean_nat_dec_le(x_769, x_769);
if (x_772 == 0)
{
if (x_770 == 0)
{
lean_dec_ref(x_739);
lean_dec(x_6);
goto block_758;
}
else
{
size_t x_773; size_t x_774; lean_object* x_775; 
x_773 = 0;
x_774 = lean_usize_of_nat(x_769);
x_775 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_739, x_773, x_774, x_771, x_6);
lean_dec(x_6);
lean_dec_ref(x_739);
x_759 = x_775;
goto block_768;
}
}
else
{
size_t x_776; size_t x_777; lean_object* x_778; 
x_776 = 0;
x_777 = lean_usize_of_nat(x_769);
x_778 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(x_739, x_776, x_777, x_771, x_6);
lean_dec(x_6);
lean_dec_ref(x_739);
x_759 = x_778;
goto block_768;
}
}
}
block_781:
{
if (x_780 == 0)
{
lean_inc_ref(x_740);
lean_inc_ref(x_739);
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_del_object(x_639);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec_ref(x_5);
goto block_779;
}
else
{
if (x_141 == 0)
{
x_710 = x_3;
x_711 = x_5;
x_712 = x_6;
x_713 = x_223;
x_714 = x_8;
goto block_735;
}
else
{
lean_inc_ref(x_740);
lean_inc_ref(x_739);
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_del_object(x_639);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec_ref(x_5);
goto block_779;
}
}
}
}
else
{
lean_object* x_796; lean_object* x_797; 
lean_inc_ref(x_738);
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_del_object(x_639);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_796 = lean_ctor_get(x_738, 0);
lean_inc_ref(x_796);
lean_dec_ref(x_738);
if (x_617 == 0)
{
lean_ctor_set(x_616, 0, x_796);
x_797 = x_616;
goto block_798;
}
else
{
lean_object* x_799; 
x_799 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_799, 0, x_796);
x_797 = x_799;
goto block_798;
}
block_798:
{
return x_797;
}
}
}
block_668:
{
lean_object* x_648; 
x_648 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_647);
lean_dec(x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; uint8_t x_650; uint8_t x_658; 
x_658 = !lean_is_exclusive(x_648);
if (x_658 == 0)
{
lean_object* x_659; 
x_659 = lean_ctor_get(x_648, 0);
lean_dec(x_659);
x_649 = x_648;
x_650 = x_658;
goto block_657;
}
else
{
lean_dec(x_648);
x_649 = lean_box(0);
x_650 = x_658;
goto block_657;
}
block_657:
{
lean_object* x_651; 
if (x_634 == 0)
{
lean_ctor_set_tag(x_633, 6);
lean_ctor_set(x_633, 0, x_646);
x_651 = x_633;
goto block_655;
}
else
{
lean_object* x_656; 
x_656 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_656, 0, x_646);
x_651 = x_656;
goto block_655;
}
block_655:
{
lean_object* x_652; 
if (x_650 == 0)
{
lean_ctor_set(x_649, 0, x_651);
x_652 = x_649;
goto block_653;
}
else
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_654, 0, x_651);
x_652 = x_654;
goto block_653;
}
block_653:
{
return x_652;
}
}
}
}
else
{
lean_object* x_660; lean_object* x_661; uint8_t x_662; uint8_t x_667; 
lean_dec_ref(x_646);
lean_del_object(x_633);
x_660 = lean_ctor_get(x_648, 0);
x_667 = !lean_is_exclusive(x_648);
if (x_667 == 0)
{
x_661 = x_648;
x_662 = x_667;
goto block_666;
}
else
{
lean_inc(x_660);
lean_dec(x_648);
x_661 = lean_box(0);
x_662 = x_667;
goto block_666;
}
block_666:
{
lean_object* x_663; 
if (x_662 == 0)
{
x_663 = x_661;
goto block_664;
}
else
{
lean_object* x_665; 
x_665 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_665, 0, x_660);
x_663 = x_665;
goto block_664;
}
block_664:
{
return x_663;
}
}
}
}
block_679:
{
if (lean_obj_tag(x_670) == 0)
{
lean_dec_ref(x_670);
x_647 = x_669;
goto block_668;
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_678; 
lean_dec(x_669);
lean_dec_ref(x_646);
lean_del_object(x_633);
x_671 = lean_ctor_get(x_670, 0);
x_678 = !lean_is_exclusive(x_670);
if (x_678 == 0)
{
x_672 = x_670;
x_673 = x_678;
goto block_677;
}
else
{
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_box(0);
x_673 = x_678;
goto block_677;
}
block_677:
{
lean_object* x_674; 
if (x_673 == 0)
{
x_674 = x_672;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_671);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
}
block_695:
{
uint8_t x_686; 
x_686 = lean_nat_dec_lt(x_636, x_684);
if (x_686 == 0)
{
lean_dec_ref(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec_ref(x_682);
lean_dec(x_681);
lean_dec(x_642);
x_647 = x_680;
goto block_668;
}
else
{
lean_object* x_687; uint8_t x_688; 
x_687 = lean_box(0);
x_688 = lean_nat_dec_le(x_684, x_684);
if (x_688 == 0)
{
if (x_686 == 0)
{
lean_dec_ref(x_685);
lean_dec(x_684);
lean_dec(x_683);
lean_dec_ref(x_682);
lean_dec(x_681);
lean_dec(x_642);
x_647 = x_680;
goto block_668;
}
else
{
size_t x_689; size_t x_690; lean_object* x_691; 
x_689 = 0;
x_690 = lean_usize_of_nat(x_684);
lean_dec(x_684);
x_691 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_642, x_689, x_690, x_687, x_685, x_681, x_682, x_683);
lean_dec(x_683);
lean_dec_ref(x_682);
lean_dec(x_681);
lean_dec_ref(x_685);
lean_dec(x_642);
x_669 = x_680;
x_670 = x_691;
goto block_679;
}
}
else
{
size_t x_692; size_t x_693; lean_object* x_694; 
x_692 = 0;
x_693 = lean_usize_of_nat(x_684);
lean_dec(x_684);
x_694 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(x_642, x_692, x_693, x_687, x_685, x_681, x_682, x_683);
lean_dec(x_683);
lean_dec_ref(x_682);
lean_dec(x_681);
lean_dec_ref(x_685);
lean_dec(x_642);
x_669 = x_680;
x_670 = x_694;
goto block_679;
}
}
}
block_703:
{
lean_object* x_696; 
if (x_627 == 0)
{
lean_ctor_set(x_626, 3, x_642);
lean_ctor_set(x_626, 2, x_632);
lean_ctor_set(x_626, 1, x_646);
x_696 = x_626;
goto block_701;
}
else
{
lean_object* x_702; 
x_702 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_702, 0, x_622);
lean_ctor_set(x_702, 1, x_646);
lean_ctor_set(x_702, 2, x_632);
lean_ctor_set(x_702, 3, x_642);
x_696 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_697; lean_object* x_698; 
x_697 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_697, 0, x_696);
if (x_644 == 0)
{
lean_ctor_set(x_643, 0, x_697);
x_698 = x_643;
goto block_699;
}
else
{
lean_object* x_700; 
x_700 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_700, 0, x_697);
x_698 = x_700;
goto block_699;
}
block_699:
{
return x_698;
}
}
}
block_709:
{
if (x_704 == 0)
{
lean_del_object(x_639);
lean_dec(x_624);
lean_dec_ref(x_1);
goto block_703;
}
else
{
uint8_t x_705; 
x_705 = l_Lean_instBEqFVarId_beq(x_624, x_632);
lean_dec(x_624);
if (x_705 == 0)
{
lean_del_object(x_639);
lean_dec_ref(x_1);
goto block_703;
}
else
{
lean_object* x_706; 
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec(x_622);
if (x_640 == 0)
{
lean_ctor_set(x_639, 0, x_1);
x_706 = x_639;
goto block_707;
}
else
{
lean_object* x_708; 
x_708 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_708, 0, x_1);
x_706 = x_708;
goto block_707;
}
block_707:
{
return x_706;
}
}
}
}
block_735:
{
lean_object* x_715; uint8_t x_716; 
x_715 = lean_array_get_size(x_642);
x_716 = lean_nat_dec_lt(x_636, x_715);
if (x_716 == 0)
{
lean_del_object(x_643);
lean_del_object(x_639);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_680 = x_710;
x_681 = x_712;
x_682 = x_713;
x_683 = x_714;
x_684 = x_715;
x_685 = x_711;
goto block_695;
}
else
{
if (x_716 == 0)
{
lean_del_object(x_643);
lean_del_object(x_639);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_680 = x_710;
x_681 = x_712;
x_682 = x_713;
x_683 = x_714;
x_684 = x_715;
x_685 = x_711;
goto block_695;
}
else
{
size_t x_717; size_t x_718; uint8_t x_719; 
x_717 = 0;
x_718 = lean_usize_of_nat(x_715);
x_719 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(x_128, x_129, x_642, x_717, x_718);
lean_dec(x_129);
lean_dec(x_128);
if (x_719 == 0)
{
lean_del_object(x_643);
lean_del_object(x_639);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
x_680 = x_710;
x_681 = x_712;
x_682 = x_713;
x_683 = x_714;
x_684 = x_715;
x_685 = x_711;
goto block_695;
}
else
{
if (x_141 == 0)
{
lean_object* x_720; 
lean_dec(x_714);
lean_dec_ref(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_del_object(x_633);
lean_inc(x_632);
x_720 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_632, x_710);
lean_dec(x_710);
if (lean_obj_tag(x_720) == 0)
{
size_t x_721; size_t x_722; uint8_t x_723; 
lean_dec_ref(x_720);
x_721 = lean_ptr_addr(x_625);
lean_dec_ref(x_625);
x_722 = lean_ptr_addr(x_642);
x_723 = lean_usize_dec_eq(x_721, x_722);
if (x_723 == 0)
{
lean_dec_ref(x_623);
x_704 = x_723;
goto block_709;
}
else
{
size_t x_724; size_t x_725; uint8_t x_726; 
x_724 = lean_ptr_addr(x_623);
lean_dec_ref(x_623);
x_725 = lean_ptr_addr(x_646);
x_726 = lean_usize_dec_eq(x_724, x_725);
x_704 = x_726;
goto block_709;
}
}
else
{
lean_object* x_727; lean_object* x_728; uint8_t x_729; uint8_t x_734; 
lean_dec_ref(x_646);
lean_del_object(x_643);
lean_dec(x_642);
lean_del_object(x_639);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
x_727 = lean_ctor_get(x_720, 0);
x_734 = !lean_is_exclusive(x_720);
if (x_734 == 0)
{
x_728 = x_720;
x_729 = x_734;
goto block_733;
}
else
{
lean_inc(x_727);
lean_dec(x_720);
x_728 = lean_box(0);
x_729 = x_734;
goto block_733;
}
block_733:
{
lean_object* x_730; 
if (x_729 == 0)
{
x_730 = x_728;
goto block_731;
}
else
{
lean_object* x_732; 
x_732 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_732, 0, x_727);
x_730 = x_732;
goto block_731;
}
block_731:
{
return x_730;
}
}
}
}
else
{
lean_del_object(x_643);
lean_del_object(x_639);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec_ref(x_1);
x_680 = x_710;
x_681 = x_712;
x_682 = x_713;
x_683 = x_714;
x_684 = x_715;
x_685 = x_711;
goto block_695;
}
}
}
}
}
}
}
else
{
lean_object* x_802; lean_object* x_803; uint8_t x_804; uint8_t x_809; 
lean_del_object(x_639);
lean_dec(x_635);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_del_object(x_616);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_802 = lean_ctor_get(x_641, 0);
x_809 = !lean_is_exclusive(x_641);
if (x_809 == 0)
{
x_803 = x_641;
x_804 = x_809;
goto block_808;
}
else
{
lean_inc(x_802);
lean_dec(x_641);
x_803 = lean_box(0);
x_804 = x_809;
goto block_808;
}
block_808:
{
lean_object* x_805; 
if (x_804 == 0)
{
x_805 = x_803;
goto block_806;
}
else
{
lean_object* x_807; 
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_802);
x_805 = x_807;
goto block_806;
}
block_806:
{
return x_805;
}
}
}
}
}
else
{
lean_object* x_812; lean_object* x_813; uint8_t x_814; uint8_t x_819; 
lean_dec(x_635);
lean_del_object(x_633);
lean_dec(x_632);
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_del_object(x_616);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_812 = lean_ctor_get(x_637, 0);
x_819 = !lean_is_exclusive(x_637);
if (x_819 == 0)
{
x_813 = x_637;
x_814 = x_819;
goto block_818;
}
else
{
lean_inc(x_812);
lean_dec(x_637);
x_813 = lean_box(0);
x_814 = x_819;
goto block_818;
}
block_818:
{
lean_object* x_815; 
if (x_814 == 0)
{
x_815 = x_813;
goto block_816;
}
else
{
lean_object* x_817; 
x_817 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_817, 0, x_812);
x_815 = x_817;
goto block_816;
}
block_816:
{
return x_815;
}
}
}
}
}
else
{
lean_object* x_822; 
lean_del_object(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_del_object(x_616);
lean_dec_ref(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_822 = l_Lean_Compiler_LCNF_mkReturnErased(x_630, x_5, x_6, x_223, x_8);
lean_dec(x_8);
lean_dec_ref(x_223);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_822;
}
}
}
}
}
else
{
lean_object* x_827; lean_object* x_828; uint8_t x_829; uint8_t x_834; 
lean_dec_ref(x_613);
lean_dec_ref(x_1);
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_827 = lean_ctor_get(x_614, 0);
x_834 = !lean_is_exclusive(x_614);
if (x_834 == 0)
{
x_828 = x_614;
x_829 = x_834;
goto block_833;
}
else
{
lean_inc(x_827);
lean_dec(x_614);
x_828 = lean_box(0);
x_829 = x_834;
goto block_833;
}
block_833:
{
lean_object* x_830; 
if (x_829 == 0)
{
x_830 = x_828;
goto block_831;
}
else
{
lean_object* x_832; 
x_832 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_832, 0, x_827);
x_830 = x_832;
goto block_831;
}
block_831:
{
return x_830;
}
}
}
}
case 5:
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_del_object(x_145);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_835 = lean_ctor_get(x_1, 0);
x_836 = lean_st_ref_get(x_3);
x_837 = lean_ctor_get(x_836, 0);
lean_inc_ref(x_837);
lean_dec(x_836);
lean_inc(x_835);
x_838 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_837, x_835, x_141);
lean_dec_ref(x_837);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; 
lean_dec_ref(x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
lean_dec_ref(x_838);
lean_inc(x_839);
x_840 = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(x_839, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; uint8_t x_842; uint8_t x_859; 
x_859 = !lean_is_exclusive(x_840);
if (x_859 == 0)
{
lean_object* x_860; 
x_860 = lean_ctor_get(x_840, 0);
lean_dec(x_860);
x_841 = x_840;
x_842 = x_859;
goto block_858;
}
else
{
lean_dec(x_840);
x_841 = lean_box(0);
x_842 = x_859;
goto block_858;
}
block_858:
{
uint8_t x_843; 
x_843 = l_Lean_instBEqFVarId_beq(x_835, x_839);
if (x_843 == 0)
{
lean_object* x_844; uint8_t x_845; uint8_t x_853; 
x_853 = !lean_is_exclusive(x_1);
if (x_853 == 0)
{
lean_object* x_854; 
x_854 = lean_ctor_get(x_1, 0);
lean_dec(x_854);
x_844 = x_1;
x_845 = x_853;
goto block_852;
}
else
{
lean_dec(x_1);
x_844 = lean_box(0);
x_845 = x_853;
goto block_852;
}
block_852:
{
lean_object* x_846; 
if (x_845 == 0)
{
lean_ctor_set(x_844, 0, x_839);
x_846 = x_844;
goto block_850;
}
else
{
lean_object* x_851; 
x_851 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_851, 0, x_839);
x_846 = x_851;
goto block_850;
}
block_850:
{
lean_object* x_847; 
if (x_842 == 0)
{
lean_ctor_set(x_841, 0, x_846);
x_847 = x_841;
goto block_848;
}
else
{
lean_object* x_849; 
x_849 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_849, 0, x_846);
x_847 = x_849;
goto block_848;
}
block_848:
{
return x_847;
}
}
}
}
else
{
lean_object* x_855; 
lean_dec(x_839);
if (x_842 == 0)
{
lean_ctor_set(x_841, 0, x_1);
x_855 = x_841;
goto block_856;
}
else
{
lean_object* x_857; 
x_857 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_857, 0, x_1);
x_855 = x_857;
goto block_856;
}
block_856:
{
return x_855;
}
}
}
}
else
{
lean_object* x_861; lean_object* x_862; uint8_t x_863; uint8_t x_868; 
lean_dec(x_839);
lean_dec_ref(x_1);
x_861 = lean_ctor_get(x_840, 0);
x_868 = !lean_is_exclusive(x_840);
if (x_868 == 0)
{
x_862 = x_840;
x_863 = x_868;
goto block_867;
}
else
{
lean_inc(x_861);
lean_dec(x_840);
x_862 = lean_box(0);
x_863 = x_868;
goto block_867;
}
block_867:
{
lean_object* x_864; 
if (x_863 == 0)
{
x_864 = x_862;
goto block_865;
}
else
{
lean_object* x_866; 
x_866 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_866, 0, x_861);
x_864 = x_866;
goto block_865;
}
block_865:
{
return x_864;
}
}
}
}
else
{
uint8_t x_869; lean_object* x_870; 
lean_dec_ref(x_1);
lean_dec(x_3);
x_869 = 0;
x_870 = l_Lean_Compiler_LCNF_mkReturnErased(x_869, x_5, x_6, x_223, x_8);
lean_dec(x_8);
lean_dec_ref(x_223);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_870;
}
}
case 6:
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; lean_object* x_875; size_t x_876; size_t x_877; uint8_t x_878; 
lean_dec_ref(x_223);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_871 = lean_ctor_get(x_1, 0);
x_872 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_873 = lean_ctor_get(x_872, 0);
lean_inc_ref(x_873);
lean_dec(x_872);
x_874 = 0;
lean_inc_ref(x_871);
x_875 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_874, x_873, x_141, x_871);
lean_dec_ref(x_873);
x_876 = lean_ptr_addr(x_871);
x_877 = lean_ptr_addr(x_875);
x_878 = lean_usize_dec_eq(x_876, x_877);
if (x_878 == 0)
{
lean_object* x_879; uint8_t x_880; uint8_t x_888; 
x_888 = !lean_is_exclusive(x_1);
if (x_888 == 0)
{
lean_object* x_889; 
x_889 = lean_ctor_get(x_1, 0);
lean_dec(x_889);
x_879 = x_1;
x_880 = x_888;
goto block_887;
}
else
{
lean_dec(x_1);
x_879 = lean_box(0);
x_880 = x_888;
goto block_887;
}
block_887:
{
lean_object* x_881; 
if (x_880 == 0)
{
lean_ctor_set(x_879, 0, x_875);
x_881 = x_879;
goto block_885;
}
else
{
lean_object* x_886; 
x_886 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_886, 0, x_875);
x_881 = x_886;
goto block_885;
}
block_885:
{
lean_object* x_882; 
if (x_146 == 0)
{
lean_ctor_set(x_145, 0, x_881);
x_882 = x_145;
goto block_883;
}
else
{
lean_object* x_884; 
x_884 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_884, 0, x_881);
x_882 = x_884;
goto block_883;
}
block_883:
{
return x_882;
}
}
}
}
else
{
lean_object* x_890; 
lean_dec_ref(x_875);
if (x_146 == 0)
{
lean_ctor_set(x_145, 0, x_1);
x_890 = x_145;
goto block_891;
}
else
{
lean_object* x_892; 
x_892 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_892, 0, x_1);
x_890 = x_892;
goto block_891;
}
block_891:
{
return x_890;
}
}
}
default: 
{
lean_object* x_893; lean_object* x_894; 
lean_del_object(x_145);
lean_dec(x_129);
lean_dec(x_128);
x_893 = lean_ctor_get(x_1, 0);
x_894 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_894);
lean_inc_ref(x_893);
x_147 = x_893;
x_148 = x_894;
x_149 = x_2;
x_150 = x_3;
x_151 = x_4;
x_152 = x_5;
x_153 = x_6;
x_154 = x_223;
x_155 = x_8;
goto block_220;
}
}
}
}
}
else
{
lean_object* x_900; lean_object* x_901; uint8_t x_902; uint8_t x_907; 
lean_del_object(x_142);
lean_dec_ref(x_140);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_900 = lean_ctor_get(x_144, 0);
x_907 = !lean_is_exclusive(x_144);
if (x_907 == 0)
{
x_901 = x_144;
x_902 = x_907;
goto block_906;
}
else
{
lean_inc(x_900);
lean_dec(x_144);
x_901 = lean_box(0);
x_902 = x_907;
goto block_906;
}
block_906:
{
lean_object* x_903; 
if (x_902 == 0)
{
x_903 = x_901;
goto block_904;
}
else
{
lean_object* x_905; 
x_905 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_905, 0, x_900);
x_903 = x_905;
goto block_904;
}
block_904:
{
return x_903;
}
}
}
}
}
else
{
lean_object* x_924; 
lean_dec_ref(x_1);
x_924 = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_924;
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
block_45:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ptr_addr(x_27);
x_29 = lean_ptr_addr(x_24);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
x_17 = x_24;
x_18 = x_25;
x_19 = x_30;
goto block_23;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = lean_ptr_addr(x_26);
x_32 = lean_ptr_addr(x_25);
x_33 = lean_usize_dec_eq(x_31, x_32);
x_17 = x_24;
x_18 = x_25;
x_19 = x_33;
goto block_23;
}
}
case 2:
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ptr_addr(x_35);
x_37 = lean_ptr_addr(x_24);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
x_10 = x_24;
x_11 = x_25;
x_12 = x_38;
goto block_16;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = lean_ptr_addr(x_34);
x_40 = lean_ptr_addr(x_25);
x_41 = lean_usize_dec_eq(x_39, x_40);
x_10 = x_24;
x_11 = x_25;
x_12 = x_41;
goto block_16;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_42 = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simp___closed__3, &l_Lean_Compiler_LCNF_Simp_simp___closed__3_once, _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3);
x_43 = l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
block_96:
{
lean_object* x_56; 
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc(x_53);
lean_inc_ref(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
x_56 = l_Lean_Compiler_LCNF_Simp_simp(x_47, x_49, x_50, x_51, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_48, 0);
x_59 = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(x_58, x_50);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_1);
x_62 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(x_48, x_50, x_53);
lean_dec(x_53);
lean_dec(x_50);
lean_dec_ref(x_48);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; uint8_t x_69; 
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_62, 0);
lean_dec(x_70);
x_63 = x_62;
x_64 = x_69;
goto block_68;
}
else
{
lean_dec(x_62);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_57);
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_57);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_57);
x_71 = lean_ctor_get(x_62, 0);
x_78 = !lean_is_exclusive(x_62);
if (x_78 == 0)
{
x_72 = x_62;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
if (x_46 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
x_24 = x_57;
x_25 = x_48;
goto block_45;
}
else
{
lean_object* x_79; 
lean_inc_ref(x_48);
x_79 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_79) == 0)
{
lean_dec_ref(x_79);
x_24 = x_57;
x_25 = x_48;
goto block_45;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec(x_57);
lean_dec_ref(x_48);
lean_dec_ref(x_1);
x_80 = lean_ctor_get(x_79, 0);
x_87 = !lean_is_exclusive(x_79);
if (x_87 == 0)
{
x_81 = x_79;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_79);
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
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_59, 0);
x_95 = !lean_is_exclusive(x_59);
if (x_95 == 0)
{
x_89 = x_59;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_59);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_1);
return x_56;
}
}
block_117:
{
lean_object* x_107; 
lean_inc(x_106);
lean_inc_ref(x_105);
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc_ref(x_100);
x_107 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_46 = x_97;
x_47 = x_98;
x_48 = x_108;
x_49 = x_100;
x_50 = x_101;
x_51 = x_102;
x_52 = x_103;
x_53 = x_104;
x_54 = x_105;
x_55 = x_106;
goto block_96;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_98);
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_107, 0);
x_116 = !lean_is_exclusive(x_107);
if (x_116 == 0)
{
x_110 = x_107;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_107);
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
block_124:
{
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_1);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_118);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
else
{
lean_object* x_123; 
lean_dec_ref(x_119);
lean_dec_ref(x_118);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_1);
return x_123;
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
